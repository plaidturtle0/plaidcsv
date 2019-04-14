extern crate clap;
extern crate csv;
extern crate regex;
extern crate approx;
use std::error;
use std::error::Error;
use std::fmt;
use std::collections::HashMap;
use std::process::exit;
use std::io;
use std::cmp::Ordering;
use clap::{Arg, App};
use sqlparser::dialect::GenericSqlDialect;
use sqlparser::sqlparser::Parser;
use sqlparser::sqlast::{ASTNode,SQLOrderByExpr,Value,SQLOperator,SQLStatement,SQLSetExpr,TableFactor, SQLObjectName,SQLQuery,SQLSelectItem};
use sqlparser::sqlast::ASTNode::{SQLIdentifier,SQLValue,SQLBinaryExpr,SQLUnary,SQLFunction};
use sqlparser::sqlast::SQLSelectItem::{UnnamedExpression,ExpressionWithAlias,QualifiedWildcard,Wildcard};
use csv::{Reader,ReaderBuilder,Writer,WriterBuilder,StringRecord};
use regex::Regex;
use approx::abs_diff_eq;

use crate::CSVCell::{VFlt,VInt,VStr,VEmp,VBool};

#[derive(Debug, Clone)]
struct NotImplError;
impl error::Error for NotImplError {
  fn description(&self) -> &str {
    "Not implemented"
  }
  fn cause(&self) -> Option<&error::Error> {
    None
  }
}
impl fmt::Display for NotImplError {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}", self.description())
  }
}

#[derive(Debug, Clone)]
struct NotImplReasonError {
  err:String
}
impl error::Error for NotImplReasonError {
  fn description(&self) -> &str {
    &self.err
  }
  fn cause(&self) -> Option<&error::Error> {
    None
  }
}
impl fmt::Display for NotImplReasonError {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}", self.description())
  }
}

#[derive(Debug, Clone)]
struct SqlError {
  err:String
}
impl error::Error for SqlError {
  fn description(&self) -> &str {
    &self.err
  }
  fn cause(&self) -> Option<&error::Error> {
    None
  }
}
impl fmt::Display for SqlError {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}", self.description())
  }
}

#[derive(Debug)]
struct CSVOptions {
  headers: bool,
  delimiter: u8
}

#[derive(Debug,Clone)]
enum CSVCell {
  VInt(i64),
  VFlt(f64),
  VStr(String),
  VBool(bool),
  VEmp
}

enum FnType {
  Scalar,
  Aggregate
}

struct TableRow {
  data: Vec<CSVCell>
}

fn parse_field( field: &str ) -> CSVCell {
  if let Ok(f) = field.parse::<i64>() {
    return VInt(f);
  }
  if let Ok(f) = field.parse::<f64>() {
    return VFlt(f);
  }
  return VStr(field.to_string());
}

fn format_field( field: &CSVCell ) -> String {
  match field {
    VInt(i) => i.to_string(),
    VFlt(i) => i.to_string(),
    VStr(i) => i.to_string(),
    VBool(i) => (*i as i32).to_string(),
    VEmp => "{missing column}".to_string()
  }
}
impl fmt::Display for CSVCell {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}", format_field(&self))
  }
}

fn parse_row( row: &StringRecord ) -> TableRow {
  let mut data = Vec::new();
  for field in row.iter() {
    data.push(parse_field(field));
  }
  return TableRow {
    data: data
  }
}

fn format_row( row: &TableRow ) -> StringRecord {
  let mut record = StringRecord::new();
  for cell in row.data.iter() {
    record.push_field(&format_field(cell));
  }
  record
}

struct ViewMetadata {
  line: i64,
  headers: Option<StringRecord>,
  header_lookup: HashMap<String, usize>
}

fn field_lookup(meta: &ViewMetadata, row: &TableRow, field: &str) -> CSVCell {
  match meta.header_lookup.get(field) {
    None => VEmp,
    Some(i) => row.data.get(*i).unwrap_or(&VEmp).clone()
  }
}

trait GenericView {
  fn headers(&mut self) -> &Option<StringRecord>;
  fn next(&mut self) -> Result<Option<TableRow>,Box<Error>>;
  fn field(&self, row: &TableRow, field: &str) -> CSVCell;
  fn linenum(&self) -> i64;
}

fn write_view<T>(view: &mut GenericView, writer: &mut Writer<T>) -> Result<(),Box<Error>>
  where T: std::io::Write {
  if let Some(hdr) = view.headers() {
    writer.write_record(hdr)?
  }
  while let Some(row) = view.next()? {
    writer.write_record(&format_row(&row))?;
  }
  return Ok(())
}

struct FileView<T> {
  rdr:Reader<T>,
  meta:ViewMetadata
}

fn make_lookup( hdr : &Option<StringRecord> ) -> HashMap<String,usize> {
  let mut map = HashMap::new();
  if let Some(headers) = hdr {
    for (i, field) in headers.iter().enumerate() {
      map.insert(field.to_string(), i);
    }
  }
  map
}

fn make_stdin_view(available: &mut bool, opts: &CSVOptions) -> Result<Box<GenericView>, Box<Error>> {
  if *available {
    *available=false;
  } else {
    return Err(make_sql_err(None, "You can only read from stdin once"))
  }
  let reader = ReaderBuilder::new()
    .delimiter(opts.delimiter)
    .has_headers(false)
    .from_reader(io::stdin());
  make_reader_view(reader, opts)
}

fn make_file_view(path : &str, opts : &CSVOptions) -> Result<Box<GenericView>, Box<Error>> {
  let reader = ReaderBuilder::new()
    .delimiter(opts.delimiter)
    .has_headers(false)
    .from_path(path)?;
  make_reader_view(reader, opts)
}

fn make_reader_view<T>(mut reader: csv::Reader<T>, opts : &CSVOptions) -> Result<Box<GenericView>, Box<Error>>
  where T: std::io::Read, T: 'static {
  let hdrs = if opts.headers { Some(reader.records().next().unwrap().unwrap().clone()) } else { None };
  Ok(Box::new(FileView{
    meta : ViewMetadata {
      line: 0,
      header_lookup: make_lookup(&hdrs),
      headers: hdrs,
    },
    rdr : reader
  }))
}

impl<T> GenericView for FileView<T>
  where T: std::io::Read {
  fn next(&mut self) -> Result<Option<TableRow>,Box<Error>> {
    match self.rdr.records().next() {
      Some(result) => {
        self.meta.line += 1;
        Ok(Some(parse_row(&result?)))
      },
      None => Ok(None)
    }
  }
  fn headers(&mut self) -> &Option<StringRecord> {
    return &self.meta.headers;
  }
  fn field(&self, row: &TableRow, field: &str) -> CSVCell {
    field_lookup(&self.meta, row, field)
  }
  fn linenum(&self) -> i64 {
    return self.meta.line;
  }
}

struct SelectView {
  projection: Vec<SQLSelectItem>,
  relation: Box<GenericView>,
  selection: Option<ASTNode>,
  // omitted: joins, group_by, having
  meta: ViewMetadata
}

struct AggregateView {
  fns: Vec<Box<AggregateFn>>,
  source: Box<GenericView>,
  meta: ViewMetadata
}

struct LimitView {
  limit: i64,
  source: Box<GenericView>,
  meta: ViewMetadata
}

struct SortedView {
  cache: Option<Vec<TableRow>>,
  order_by: Vec<SQLOrderByExpr>,
  source: Box<GenericView>,
  meta: ViewMetadata
}

trait AggregateFn {
  fn accumulate(&mut self, cell: &CSVCell) -> Result<(), Box<Error>>;
  fn output(&self) -> Result<CSVCell, Box<Error>>;
}

struct SumFn {
  sum: Option<CSVCell>
}
impl SumFn {
  fn new() -> Self {
    SumFn { sum: None }
  }
}
impl AggregateFn for SumFn {
  fn accumulate(&mut self, cell: &CSVCell) -> Result<(), Box<Error>> {
    self.sum = match (&self.sum, cell) {
      (None, VInt(i)) => Some(VInt(*i)),
      (None, VFlt(i)) => Some(VFlt(*i)),
      (None, _) => return Err(make_sql_err(None, &format!("Can't SUM {}", cell))),
      (Some(l), r) => Some(eval_bin_op(&l,&r,&SQLOperator::Plus)?)
    };
    Ok(())
  }
  fn output(&self) -> Result<CSVCell, Box<Error>> {
    match &self.sum {
      None => Ok(VInt(0)),
      Some(x) => Ok(x.clone())
    }
  }
}

struct CountFn {
  count: i64
}
impl CountFn {
  fn new() -> Self {
    CountFn{ count: 0 }
  }
}
impl AggregateFn for CountFn {
  fn accumulate(&mut self, _: &CSVCell) -> Result<(), Box<Error>> {
    self.count += 1;
    Ok(())
  }
  fn output(&self) -> Result<CSVCell, Box<Error>> {
    Ok(VInt(self.count))
  }
}

struct MaxFn {
  max: Option<CSVCell>,
  gt: SQLOperator
}
impl MaxFn {
  fn new(gt: SQLOperator) -> Self {
    MaxFn { max: None, gt: gt }
  }
}
impl AggregateFn for MaxFn {
  fn accumulate(&mut self, cell: &CSVCell) -> Result<(), Box<Error>> {
    self.max = match (&self.max, cell) {
      (None, VInt(i)) => Some(VInt(*i)),
      (None, VFlt(i)) => Some(VFlt(*i)),
      (None, _) => return Err(make_sql_err(None, &format!("Can't MAX/MIN {}", cell))),
      (Some(l), r) => {
        match eval_bin_op(&r,&l,&self.gt)? {
          VBool(true) => Some(r.clone()),
          VBool(false) => Some(l.clone()),
          _ => return Err(make_sql_err(None, &format!("Can't compare {} to {}", l, r)))
        }
      }
    };
    Ok(())
  }
  fn output(&self) -> Result<CSVCell, Box<Error>> {
    match &self.max {
      None => Err(make_sql_err(None, &format!("Can't take MAX/MIN of no values"))),
      Some(x) => Ok(x.clone())
    }
  }
}

struct AvgFn {
  sum: f64,
  count: i64
}
impl AvgFn {
  fn new() -> Self {
    AvgFn { sum: 0.0, count: 0 }
  }
}
impl AggregateFn for AvgFn {
  fn accumulate(&mut self, cell: &CSVCell) -> Result<(), Box<Error>> {
    self.count += 1;
    self.sum += match cell {
      VInt(i) => *i as f64,
      VFlt(i) => *i,
      _ => return Err(make_sql_err(None, &format!("Can't AVG {}", cell))),
    };
    Ok(())
  }
  fn output(&self) -> Result<CSVCell, Box<Error>> {
    match &self.count {
      0 => Err(make_sql_err(None, &format!("Can't take AVG of no values"))),
      _ => Ok(VFlt(self.sum/(self.count as f64)))
    }
  }
}

fn get_aggregate_fn(id:&str) -> Option<Box<AggregateFn>> {
  match id.to_uppercase().as_ref() {
    "SUM" => Some(Box::new(SumFn::new())),
    "MAX" => Some(Box::new(MaxFn::new(SQLOperator::Gt))),
    "MIN" => Some(Box::new(MaxFn::new(SQLOperator::Lt))),
    "COUNT" => Some(Box::new(CountFn::new())),
    "AVG" => Some(Box::new(AvgFn::new())),
    _ => None
  }
}

fn get_node_from_select_item( item: &SQLSelectItem) -> Option<&ASTNode> {
  match item {
    UnnamedExpression(node) => Some(node),
    ExpressionWithAlias(node,_) => Some(node),
    _ => None
  }
}

fn is_aggregate( proj: Vec<SQLSelectItem> ) -> (Option<Vec<Box<AggregateFn>>>, Vec<SQLSelectItem>) {
  let mut aggregate = true;
  for item in proj.iter() {
    if let Some(SQLFunction{id, args}) = get_node_from_select_item(item) {
      match function_type(id) {
        FnType::Scalar => aggregate = false,
        FnType::Aggregate => {
          if args.len() != 1 {
            aggregate = false;
          }
        }
      }
    } else {
      aggregate = false;
    }
  }
  if !aggregate {
    return (None, proj);
  } else {
    let mut fns:Vec<Box<AggregateFn>> = Vec::new();
    let mut retproj:Vec<SQLSelectItem> = Vec::new();
    for item in proj {
      // Always matches assuming get_aggregate_fn and function_type are in sync
      // TODO: Aggregates are super hacky
      match item {
        UnnamedExpression(SQLFunction{id, mut args}) => {
          if let Some(agg) = get_aggregate_fn(&id) {
            fns.push(agg);
            retproj.push(UnnamedExpression(args.remove(0)));
          }
        },
        ExpressionWithAlias(SQLFunction{id, mut args}, alias) => {
          if let Some(agg) = get_aggregate_fn(&id) {
            fns.push(agg);
            retproj.push(ExpressionWithAlias(args.remove(0), alias));
          }
        },
        _ => panic!("Unreachable")
      }
    }
    return (Some(fns), retproj)
  }
}

fn make_sql_err( node : Option<&ASTNode>, msg : &str ) -> Box<SqlError> {
  Box::new(SqlError{
    err: format!("Invalid SQL: {}.\n{:?}", msg, node)
  })
}

fn not_impl( msg : &str ) -> Box<NotImplReasonError> {
  Box::new(NotImplReasonError{
    err: format!("Not implemented: {:?}", msg)
  })
}

fn make_object_view(node: SQLObjectName, srcs: &HashMap<String,String>, opts: &CSVOptions) -> Result<Box<GenericView>, Box<Error>> {
  match srcs.get::<str>( &node.to_string() ) {
    Some (path) => make_file_view(path, opts),
    None => Err(make_sql_err(None, &format!("Not a valid table: {}", &node.to_string())))
  }
}

fn make_statement_view(node: SQLStatement, srcs: &HashMap<String,String>, opts: &CSVOptions, stdin_available: &mut bool) -> Result<Box<GenericView>, Box<Error>> {
  match node {
    SQLStatement::SQLSelect( query ) => make_query_view(query, srcs, opts, stdin_available),
    _ => Err(not_impl("Only SELECT statements supported"))
  }
}

fn make_query_view(node: SQLQuery, srcs: &HashMap<String,String>, opts: &CSVOptions, stdin_available: &mut bool) -> Result<Box<GenericView>, Box<Error>> {
  let SQLQuery{ ctes:_, body, order_by, limit } = node;
  match body {
    SQLSetExpr::Select(select) => {
      //let { projection, relation, joins:_, selection, group_by:_, having:_} = select;
      let mut src = match select.relation {
        Some(TableFactor::Table {name, alias:_}) => make_object_view(name, srcs, opts)?,
        Some(TableFactor::Derived {subquery, alias:_}) => make_query_view(*subquery, srcs, opts, stdin_available)?,
        None => make_stdin_view(stdin_available, opts)?
      };
      let headers;
      match select.projection.as_slice() {
        [] => return Err(make_sql_err(None, "Must specify at least one field to select")),
        [Wildcard] => {
          headers = src.headers().clone();
        },
        _ => {
          let mut hdr = StringRecord::new();
          for (i, proj) in select.projection.iter().enumerate() {
            match proj {
              UnnamedExpression(SQLIdentifier(id)) => hdr.push_field(id),
              UnnamedExpression(_) => hdr.push_field(&format!("Field{}", i)),
              ExpressionWithAlias(_, id) => hdr.push_field(id),
              QualifiedWildcard(_) => return Err(not_impl("Qualified wildcards")),
              Wildcard => return Err(not_impl("Wildcards within projection"))
            };
          }
          headers = Some(hdr);
        }
      };
      let lim = match limit {
        None => None,
        Some(limnode) => match eval_node(&limnode, None, None)? {
          VInt(i) => Some(i),
          _ => return Err(make_sql_err(Some(&limnode),"LIMIT must evaluate to int"))
        }
      };
      let (aggregate, proj) = is_aggregate(select.projection);
      let view = match order_by {
        None => src,
        Some(order_expr) => {
          let hdr = src.headers().clone();
          Box::new(SortedView{
            cache: None,
            order_by: order_expr,
            source: src,
            meta: ViewMetadata {
              line: 0,
              header_lookup: make_lookup(&hdr),
              headers: hdr
            }
          })
        }
      };
      let view: Box<GenericView> = Box::new(SelectView{
        projection: proj,
        relation: view,
        selection: select.selection,
        meta: ViewMetadata {
          line: 0,
          header_lookup: make_lookup(&headers),
          headers: headers.clone()
        }
      });
      let view = match aggregate {
        None => view,
        Some(fns) => {
          Box::new(AggregateView{
            fns: fns,
            source: view,
            meta: ViewMetadata {
              line: 0,
              header_lookup: make_lookup(&headers),
              headers: headers.clone()
            }
          })
        }
      };
      let view = match lim {
        None => view,
        Some(i) => {
          Box::new(LimitView{
            limit: i,
            source: view,
            meta: ViewMetadata {
              line: 0,
              header_lookup: make_lookup(&headers),
              headers: headers
            }
          })
        }
      };
      Ok(view)
    },
    _ => Err(not_impl("Only basic SELECT supported"))
  }
}

fn compare_cells(l:&CSVCell, r:&CSVCell) -> Ordering {
  // If types are comparable, sort by natural order
  if let Ok(VBool(true)) = eval_cmp_op(l, r, false, true, false) {
    return Ordering::Equal;
  };
  if let Ok(VBool(true)) = eval_cmp_op(l, r, true, false, false) {
    return Ordering::Less;
  };
  if let Ok(VBool(true)) = eval_cmp_op(l, r, false, false, true) {
    return Ordering::Greater;
  };
  // Otherwise, sort by type (arbitrary but at least consistent).
  // We can't throw errors inside sort unfortunately.
  // Note: We know they are not the same type, otherwise they would have been comparable.
  match (l,r) {
    (VInt(_), _) => Ordering::Less,
    (_, VInt(_)) => Ordering::Greater,
    (VFlt(_), _) => Ordering::Less,
    (_,VFlt(_)) => Ordering::Greater,
    (VStr(_),_) => Ordering::Less,
    (_,VStr(_)) => Ordering::Greater,
    (VBool(_),_) => Ordering::Less,
    (_,VBool(_)) => Ordering::Greater,
    (VEmp,_) => Ordering::Less,
  }
}

fn eval_cmp_op(l:&CSVCell, r:&CSVCell, lt:bool, eq:bool, gt:bool) -> Result<CSVCell,Box<Error>> {
  match (l,r) {
    (VStr(l), VStr(r)) => Ok(VBool((lt && l<r) ||
                                   (eq && l==r) ||
                                   (gt && l>r))),
    (VBool(l), VBool(r)) => Ok(VBool((lt && l<r) ||
                                     (eq && l==r) ||
                                     (gt && l>r))),
    (VEmp, VEmp) => Ok(VBool(eq)),
    (VInt(l), VInt(r)) => Ok(VBool((lt && l<r) ||
                                   (eq && l==r) ||
                                   (gt && l>r))),
    (VFlt(l), VFlt(r)) => Ok(VBool((lt && l<r) ||
                                   (eq && l==r) ||
                                   (gt && l>r))),
    (VInt(l), VFlt(r)) => { let lf = *l as f64;
                            Ok(VBool((lt && lf<*r) ||
                                     (eq && lf==*r) ||
                                     (gt && lf>*r))) },
    (VFlt(l), VInt(r)) => { let rf = *r as f64;
                            Ok(VBool((lt && *l<rf) ||
                                     (eq && *l==rf) ||
                                     (gt && *l>rf))) },
    _ => Err(make_sql_err(None, &format!("Can't compare operands {} and {}", l, r)))
  }
}

fn sql_regex(reg : &str) -> Result<Regex, regex::Error> {
  Regex::new(&format!("^{}$", reg))
}

fn eval_bin_op(l:&CSVCell, r:&CSVCell, op:&SQLOperator) -> Result<CSVCell,Box<Error>> {
  match (op,l,r) {
    (SQLOperator::Plus, VInt(l), VInt(r)) => Ok(VInt(l+r)),
    (SQLOperator::Plus, VFlt(l), VFlt(r)) => Ok(VFlt(l+r)),
    (SQLOperator::Plus, VInt(l), VFlt(r)) => Ok(VFlt((*l as f64)+r)),
    (SQLOperator::Plus, VFlt(l), VInt(r)) => Ok(VFlt(l+(*r as f64))),
    (SQLOperator::Plus, VStr(l), VStr(r)) => Ok(VStr(l.to_string() + &r)),
    (SQLOperator::Minus, VInt(l), VInt(r)) => Ok(VInt(l-r)),
    (SQLOperator::Minus, VFlt(l), VFlt(r)) => Ok(VFlt(l-r)),
    (SQLOperator::Minus, VInt(l), VFlt(r)) => Ok(VFlt((*l as f64)-r)),
    (SQLOperator::Minus, VFlt(l), VInt(r)) => Ok(VFlt(l-(*r as f64))),
    (SQLOperator::Multiply, VInt(l), VInt(r)) => Ok(VInt(l*r)),
    (SQLOperator::Multiply, VFlt(l), VFlt(r)) => Ok(VFlt(l*r)),
    (SQLOperator::Multiply, VInt(l), VFlt(r)) => Ok(VFlt((*l as f64)*r)),
    (SQLOperator::Multiply, VFlt(l), VInt(r)) => Ok(VFlt(l*(*r as f64))),
    (SQLOperator::Divide, x, VInt(0)) => Err(make_sql_err(None, &format!("Can't divide {} by zero", x))),
    (SQLOperator::Divide, VInt(l), VInt(r)) => Ok(VInt(l/r)),
    (SQLOperator::Divide, VFlt(l), VFlt(r)) => {
      if abs_diff_eq!(*r, 0.0) {
        Err(make_sql_err(None, &format!("Can't divide {} by zero", l)))
      } else {
        Ok(VFlt(l/r))
      }
    }
    (SQLOperator::Divide, VInt(l), VFlt(r)) => {
      if abs_diff_eq!(*r, 0.0) {
        Err(make_sql_err(None, &format!("Can't divide {} by zero", l)))
      } else {
        Ok(VFlt((*l as f64)/r))
      }
    }
    (SQLOperator::Divide, VFlt(l), VInt(r)) => Ok(VFlt(l/(*r as f64))),
    (SQLOperator::Modulus, x, VInt(0)) => Err(make_sql_err(None, &format!("Can't modulus {} by zero", x))),
    (SQLOperator::Modulus, VInt(l), VInt(r)) => Ok(VInt(l%r)),
    (SQLOperator::Modulus, VFlt(l), VFlt(r)) => {
      if abs_diff_eq!(*r, 0.0) {
        Err(make_sql_err(None, &format!("Can't modulus {} by zero", l)))
      } else {
        Ok(VFlt(l%r))
      }
    }
    (SQLOperator::Modulus, VInt(l), VFlt(r)) => {
      if abs_diff_eq!(*r, 0.0) {
        Err(make_sql_err(None, &format!("Can't modulus {} by zero", l)))
      } else {
        Ok(VFlt((*l as f64)%r))
      }
    }
    (SQLOperator::Modulus, VFlt(l), VInt(r)) => Ok(VFlt(l%(*r as f64))),
    (SQLOperator::Eq, VBool(l), VBool(r)) => Ok(VBool(l==r)),
    (SQLOperator::NotEq, VBool(l), VBool(r)) => Ok(VBool(l != r)),
    (SQLOperator::Eq, VEmp, VEmp) => Ok(VBool(true)),
    (SQLOperator::NotEq, VEmp, VEmp) => Ok(VBool(false)),
    (SQLOperator::Eq, _, _) => eval_cmp_op(l,r,false,true,false),
    (SQLOperator::NotEq, _, _) => eval_cmp_op(l,r,true,false,true),
    (SQLOperator::Gt, _, _) => eval_cmp_op(l,r,false,false,true),
    (SQLOperator::Lt, _, _) => eval_cmp_op(l,r,true,false,false),
    (SQLOperator::GtEq, _, _) => eval_cmp_op(l,r,false,true,true),
    (SQLOperator::LtEq, _, _) => eval_cmp_op(l,r,true,true,false),
    (SQLOperator::And, VBool(l), VBool(r)) => Ok(VBool(*l && *r)),
    (SQLOperator::Or, VBool(l), VBool(r)) => Ok(VBool(*l || *r)),
    (SQLOperator::Like, VStr(l), VStr(r)) =>  {
      let re = sql_regex(r)?;
      Ok(VBool(re.is_match(l)))
    },
    (SQLOperator::NotLike, VStr(l), VStr(r)) => {
      let re = sql_regex(r)?;
      Ok(VBool(!re.is_match(l)))
    },
    _ => Err(make_sql_err(None, &format!("Operator {:?} is not supported for operands {} and {}", &op, l, r)))
  }
}

fn eval_unary_op(exp:&CSVCell, op:&SQLOperator) -> Result<CSVCell,Box<Error>> {
  match (op,exp) {
    (SQLOperator::Minus, VInt(e)) => Ok(VInt(-e)),
    (SQLOperator::Minus, VFlt(e)) => Ok(VFlt(-e)),
    (SQLOperator::Plus, VInt(e)) => Ok(VInt(*e)),
    (SQLOperator::Plus, VFlt(e)) => Ok(VFlt(*e)),
    (SQLOperator::Not, VBool(e)) => Ok(VBool(! *e)),
    _ => Err(make_sql_err(None, &format!("Operator {:?} is not supported for operand {}", &op, exp)))
  }
}

fn function_type(id:&str) -> FnType {
  match id.to_uppercase().as_ref() {
    "LINE" => FnType::Scalar,
    "SUM" => FnType::Aggregate,
    "MAX" => FnType::Aggregate,
    "MIN" => FnType::Aggregate,
    "COUNT" => FnType::Aggregate,
    "AVG" => FnType::Aggregate,
    _ => FnType::Scalar
  }
}

fn eval_sql_function(id:&str, args:&[CSVCell], row: Option<&TableRow>, src: Option<&GenericView>) -> Result<CSVCell,Box<Error>> {
  match (id.to_uppercase().as_ref(), args) {
    ("LINE", []) =>
      match src {
        Some(src) => Ok(VInt(src.linenum())),
        None => Err(make_sql_err(None, "LINE() requires a context"))
      },
    ("LINE", _) => Err(make_sql_err(None, "LINE() takes no args")),
    ("COL", [VInt(idx)]) =>
      match row {
        Some(row) => Ok(
          if *idx >= 0 && (*idx as usize) < row.data.len() {
            row.data[*idx as usize].clone()
          } else {
            VEmp
          }
        ),
        None => Err(make_sql_err(None, "COL() requires a context"))
      },
    ("COL", _) => Err(make_sql_err(None, "COL() takes 1 arg which must be an int")),
    (x, _) =>
      match get_aggregate_fn(x) {
        Some(mut agg) => {
          for val in args.iter() {
            agg.accumulate(val)?;
          };
          agg.output()
        },
        None => Err(make_sql_err(None, &format!("Unsupported function {}", x)))
      }
  }
}

fn eval_node(node: &ASTNode, row: Option<&TableRow>, src: Option<&GenericView>) -> Result<CSVCell,Box<Error>> {
  match node {
    SQLIdentifier(id) =>
      match(row,src) {
        (Some(r), Some(s)) => Ok(s.field(r, id)),
        _ => Err(make_sql_err(Some(node), "Can't use variables here"))
      },
    SQLValue(Value::Long(i)) => Ok(VInt(*i)),
    SQLValue(Value::Double(f)) => Ok(VFlt(*f)),
    SQLValue(Value::SingleQuotedString(s)) => Ok(VStr(s.to_string())),
    SQLValue(Value::Null) => Ok(VEmp),
    SQLValue(Value::Boolean(b)) => Ok(VBool(*b)),
    SQLValue(_) => Err(make_sql_err(Some(node), "Not a supported datatype")),
    SQLBinaryExpr{left, op, right} => {
      let left = eval_node(left, row, src)?;
      let right = eval_node(right, row, src)?;
      eval_bin_op(&left, &right, &op)
    },
    SQLUnary{operator, expr} => {
      let expr = eval_node(expr, row, src)?;
      eval_unary_op(&expr, &operator)
    },
    SQLFunction{id, args} => {
      let args:Result<Vec<CSVCell>,_> = args.into_iter().map(|x| eval_node(x, row, src)).collect();
      eval_sql_function(id, args?.as_slice(), row, src)
    },
    _ => Err(Box::new(not_impl("Node type not implemented")))
  }
}
fn next_where_internal(view: &mut GenericView, sel: &ASTNode) -> Result<Option<TableRow>,Box<Error>> {
  loop {
    match view.next()? {
      Some(row) => {
        match eval_node(&sel, Some(&row), Some(view)) {
          Ok(VBool(true)) => return Ok(Some(row)),
          Ok(VBool(false)) => (),
          Ok(_) => return Err(make_sql_err(Some(sel), "WHERE must be boolean expression")),
          Err(e) => return Err(e)
        }
      },
      None => return Ok(None)
    }
  }
}

fn next_where(view: &mut GenericView, sel: &Option<ASTNode>) -> Result<Option<TableRow>,Box<Error>>{
  match sel {
    Some(node) => next_where_internal(view, node),
    None => view.next()
  }
}

impl GenericView for SelectView {
  fn next(&mut self) -> Result<Option<TableRow>,Box<Error>> {
    match next_where(&mut *self.relation, &self.selection)? {
      None => Ok(None),
      Some(src_row) => {
        self.meta.line += 1;
        match self.projection.as_slice() {
          [Wildcard] => Ok(Some(src_row)),
          _ => {
            let mut vec = Vec::new();
            for item in self.projection.iter() {
              match get_node_from_select_item(item) {
                Some(node) => vec.push(eval_node(&node, Some(&src_row), Some(&*self.relation))?),
                None => return Err(make_sql_err(None,"Wildcard not supported in select unless it is the only expression"))
              }
            }
            Ok(Some(TableRow{
              data: vec
            }))
          }
        }
      }
    }
  }
  fn headers(&mut self) -> &Option<StringRecord> {
    return &self.meta.headers;
  }
  fn field(&self, row: &TableRow, field: &str) -> CSVCell {
    field_lookup(&self.meta, row, field)
  }
  fn linenum(&self) -> i64 {
    return self.meta.line;
  }
}

impl GenericView for AggregateView {
  fn next(&mut self) -> Result<Option<TableRow>,Box<Error>> {
    if self.meta.line > 0 {
      return Ok(None);
    }
    self.meta.line += 1;

    while let Some(src_row) = self.source.next()? {
      for (i, val) in src_row.data.iter().enumerate() {
        if i >= self.fns.len() {
          break;
        }
        self.fns[i].accumulate(val)?;
      }
    }
    let mut row = TableRow {
      data : Vec::new()
    };
    for fun in self.fns.iter() {
      row.data.push(fun.output()?);
    }
    Ok(Some(row))
  }
  fn headers(&mut self) -> &Option<StringRecord> {
    return &self.meta.headers;
  }
  fn field(&self, row: &TableRow, field: &str) -> CSVCell {
    field_lookup(&self.meta, row, field)
  }
  fn linenum(&self) -> i64 {
    return self.meta.line;
  }
}

impl GenericView for LimitView {
  fn next(&mut self) -> Result<Option<TableRow>,Box<Error>> {
    if self.meta.line >= self.limit {
      Ok(None)
    } else {
      self.meta.line += 1;
      self.source.next()
    }
  }
  fn headers(&mut self) -> &Option<StringRecord> {
    return &self.meta.headers;
  }
  fn field(&self, row: &TableRow, field: &str) -> CSVCell {
    field_lookup(&self.meta, row, field)
  }
  fn linenum(&self) -> i64 {
    return self.meta.line;
  }
}

impl GenericView for SortedView {
  fn next(&mut self) -> Result<Option<TableRow>,Box<Error>> {
    if let None = self.cache {
      let mut vec = Vec::new();
      while let Some(row) = self.source.next()? {
        vec.push(row);
      }
      // Since we'll be popping from the end of the list, sort in the opposite direction
      // of what was requested
      let mut err = Ok(());
      vec.sort_by(|l, r| {
        for node in self.order_by.iter() {
          let lval = match eval_node(&node.expr, Some(l), Some(&*self.source)) {
            Ok(lv) => lv,
            Err(e) => {
              // Even if an error occurred, we must continue on,
              // but we'll throw it later
              err=Err(e);
              VEmp
            }
          };
          let rval = match eval_node(&node.expr, Some(r), Some(&*self.source)) {
            Ok(rv) => rv,
            Err(e) => {
              err=Err(e);
              VEmp
            }
          };
          let ord = compare_cells(&lval, &rval);
          if ord != Ordering::Equal {
            if let Some(false) = node.asc {
              return ord.reverse();
            } else {
              return ord;
            }
          }
        }
        Ordering::Equal
      });
      err?;
      vec.reverse();
      self.cache = Some(vec);
    };
    if let Some(ref mut rows) = self.cache {
      if let Some(row) = rows.pop() {
        self.meta.line += 1;
        Ok(Some(row))
      } else {
        Ok(None)
      }
    } else {
      panic!("Not possible");
    }
  }
  fn headers(&mut self) -> &Option<StringRecord> {
    return &self.meta.headers;
  }
  fn field(&self, row: &TableRow, field: &str) -> CSVCell {
    field_lookup(&self.meta, row, field)
  }
  fn linenum(&self) -> i64 {
    return self.meta.line;
  }
}

//https://users.rust-lang.org/t/exiting-gracefully-instead-of-panic/3758
trait Graceful<T>{
    fn graceful(self, message:&str) -> T;
}
trait GracefulUnwrap<T,E:std::fmt::Display>{
    fn graceful_unwrap(self, message:&str) -> T;
}
impl<T, E> GracefulUnwrap<T,E> for Result<T,E>
  where E: std::fmt::Display {
    fn graceful_unwrap(self, message:&str) -> T {
        match self {
            Result::Ok(val) => val,
            Result::Err(err) => {
                println!("{}: {}", message, err);
                exit(1)
            }
        }
    }
}

impl<T> Graceful<T> for Option<T> {
    fn graceful(self, message:&str) -> T{
        match self{
            Some(val) => val,
            None => {
                println!("{}", message);
                exit(1)
            }
        }
    }
}

fn main() {
  match do_main() {
    Ok(()) => (),
    Err(e) => {
      println!("{}",e);
      exit(1)
    }
  }
}

fn do_main() -> Result<(), Box<Error>>{
    let matches =
      App::new("plaidcsv")
         .version("0.1.0")
         .about("Execute SQL statements on CSV files")
         .author("Plaid Turtle 0")
         .arg(Arg::with_name("query")
              .required(true)
              .index(1))
         .arg(Arg::with_name("table")
              .short("t")
              .long("table")
              .help("Input csv file (or - for stdin)")
              .multiple(true)
              .number_of_values(1)
              .takes_value(true))
         .arg(Arg::with_name("delimiter")
              .short("d")
              .long("delim")
              .help("Delimiter")
              .takes_value(true))
         .arg(Arg::with_name("headers")
              .short("h")
              .long("headers")
              .help("Set headers=1 or headers=0 (default 0)")
              .takes_value(true))
         .get_matches();
    let query = matches.value_of("query").unwrap();
    let dialect = GenericSqlDialect {};
    let ast = match Parser::parse_sql(&dialect, query.to_string()) {
      Ok(ast) => ast,
      Err(e) => return Err(make_sql_err(None, &format!("Parse error: {:?}", e)))
    };
    eprintln!("AST: {:?}", ast);
    let opts = CSVOptions {
      headers: matches.value_of("headers").unwrap_or("1") == "1",
      delimiter: matches.value_of("delimiter").unwrap_or(",").bytes().next().unwrap(),
    };
    let mut table_lookup = HashMap::new();
    if let Some(tables) = matches.values_of("table") {
      for (i, table) in tables.enumerate() {
        table_lookup.insert(format!("t{}",i), table.to_string());
      }
    }

    eprintln!("Opts: {:?}", opts);
    eprintln!("Tables: {:?}", &table_lookup);
    for statement in ast {
      let mut stdin_available = true;
      let mut sql_view = make_statement_view( statement, &table_lookup, &opts, &mut stdin_available )?;
      let mut wtr = WriterBuilder::new()
        .delimiter(opts.delimiter)
        .has_headers(false)
        .from_writer(std::io::stdout());
      write_view(&mut *sql_view, &mut wtr)?;
    }
    Ok(())
}
