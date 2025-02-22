/-
  Copyright (c) 2024 Florian Würmseer. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Florian Würmseer
-/

import Alloy.C

open scoped Alloy.C

alloy c include <stdlib.h> <string.h> <stdio.h> <stdlib.h> <libpq-fe.h> <lean/lean.h>

namespace LibPQ

alloy c opaque_extern_type Connection => PGconn where
  finalize(ptr) :=
    PQfinish(ptr);

structure Context where
  conn: Connection

abbrev SQL := ReaderT Context IO

alloy c opaque_extern_type Result => PGresult where
  finalize(ptr) :=
    PQclear(ptr);

alloy c enum ConnectionStatus => ConnStatusType
| ok => CONNECTION_OK
| bad => CONNECTION_BAD
| started => CONNECTION_STARTED
| made => CONNECTION_MADE
| awaitingResponse => CONNECTION_AWAITING_RESPONSE
| authOk => CONNECTION_AUTH_OK
| setenv => CONNECTION_SETENV
| sslStartup => CONNECTION_SSL_STARTUP
| needed => CONNECTION_NEEDED
| checkWritable => CONNECTION_CHECK_WRITABLE
| consume => CONNECTION_CONSUME
| gssStartup => CONNECTION_GSS_STARTUP
| checkTarget => CONNECTION_CHECK_TARGET
| checkStandby => CONNECTION_CHECK_STANDBY
deriving Inhabited, BEq

alloy c enum ResultStatus => ExecStatusType
| emptyQuery => PGRES_EMPTY_QUERY
| commandOk => PGRES_COMMAND_OK
| tuplesOk => PGRES_TUPLES_OK
| copyOut => PGRES_COPY_OUT
| copyIn => PGRES_COPY_IN
| badResponse => PGRES_BAD_RESPONSE
| nonfatalError => PGRES_NONFATAL_ERROR
| fatalError => PGRES_FATAL_ERROR
| copyBoth => PGRES_COPY_BOTH
| singleTuple => PGRES_SINGLE_TUPLE
| pipelineSync => PGRES_PIPELINE_SYNC
| pipelineAborted => PGRES_PIPELINE_ABORTED
deriving Inhabited, BEq

alloy c extern "lean_pq_login"
def login (host : String) (port: String) (dbname: String) (user: String) (password: String) : IO Connection :=
  const char* hst = lean_string_cstr(host);
  const char* prt = lean_string_cstr(port);
  const char* dbnm = lean_string_cstr(dbname);
  const char* usr = lean_string_cstr(user);
  const char* pwd = lean_string_cstr(password);
  PGconn *conn;
  conn = PQsetdbLogin(hst, prt, NULL, NULL, dbnm, usr, pwd);
  return lean_io_result_mk_ok(to_lean<Connection>(conn));

alloy c extern "lean_pq_connect"
def connect (connectionInfo : String) : IO Connection :=
  const char* conninfo = lean_string_cstr(connectionInfo);
  PGconn *conn = PQconnectdb(conninfo);
  return lean_io_result_mk_ok(to_lean<Connection>(conn));

alloy c extern "lean_pq_connection_status"
def Connection.status (connection : @& Connection) : ConnectionStatus :=
  PGresult *res;
  PGconn *conn = of_lean<Connection>(connection);
  ConnStatusType status = PQstatus(conn);
  return of_lean<ConnectionStatus>(status);

alloy c extern "lean_pq_result_status"
def Result.status (result : @& Result) : ResultStatus :=
  PGresult *res;
  res = of_lean<Result>(result);
  ExecStatusType status = PQresultStatus(res);
  return of_lean<ResultStatus>(status);

alloy c extern "lean_pq_get_error_message"
def Connection.error (connection : @& Connection) : IO String :=
  PGconn *conn = of_lean<Connection>(connection);
  return lean_io_result_mk_ok(lean_mk_string(PQerrorMessage(conn)));

alloy c extern "lean_pq_fname"
def fname (result : @& Result) (column_number : USize) : IO String :=
  PGresult *res = of_lean<Result>(result);
  return lean_io_result_mk_ok(lean_mk_string(PQfname(res, column_number)));

-- TODO should the type be generic?
alloy c extern "lean_pq_get_value"
def getValue (result : @& Result) (row : USize) (col : USize) : IO String :=
  PGresult *res = of_lean<Result>(result);
  return lean_io_result_mk_ok(lean_mk_string(PQgetvalue(res, row, col)));

alloy c extern "lean_pq_n_tuples"
def nTuples (result : @& Result) : IO USize :=
  PGresult *res = of_lean<Result>(result);
  int n = PQntuples(res);
  return lean_io_result_mk_ok(lean_box_usize(n));

alloy c extern "lean_pq_n_fields"
def nFields (result : @& Result) : IO USize :=
  PGresult *res = of_lean<Result>(result);
  int n = PQnfields(res);
  return lean_io_result_mk_ok(lean_box_usize(n));

alloy c extern "lean_pq_exec"
def exec (connection : @& Connection) (query : String) : IO Result :=
  PGconn *conn = of_lean<Connection>(connection);
  PGresult *res;
  res = PQexec(conn, lean_string_cstr(query));
  return lean_io_result_mk_ok(to_lean<Result>(res));

alloy c extern "lean_pq_prepare"
def prepare (connection : @& Connection) (statementName: String) (query : String) (nParams : USize) (parameterTypes : ByteArray) : IO Result :=
  PGconn *conn = of_lean<Connection>(connection);
  const char *stmtName = lean_string_cstr(statementName);
  const char *qry = lean_string_cstr(query);
  const uint8_t *paramTypes = lean_sarray_cptr((lean_object*)parameterTypes);
  PGresult *res;
  -- TODO: Retire paramTypes if it infers using NULL?
  res = PQprepare(conn, stmtName, qry, nParams, NULL);
  return lean_io_result_mk_ok(to_lean<Result>(res));

alloy c extern "lean_pq_exec_prepared"
def execPrepared (connection : @& Connection) (statementName: String) (nParams : USize) (parameterValues : Array String) (parameterLengths : ByteArray) (parameterFormats : ByteArray) (resultFormat : USize) : IO Result :=
  const char *stmtName = lean_string_cstr(statementName);
  lean_object** objects = lean_array_cptr(parameterValues);
  PGconn *conn = of_lean<Connection>(connection);
  PGresult *res;
  const uint8_t *paramLengths = lean_sarray_cptr((lean_object*)parameterLengths);
  const uint8_t *paramFormats = lean_sarray_cptr((lean_object*)parameterLengths);
  char **values = (char**)malloc(sizeof(void*)*nParams);
  for (int i = 0; i < nParams; i++) {
    char* current = (char*)lean_string_cstr(objects[i]);
    values[i] = current;
  }
  const char *const *paramValues = (const char *const*)values;
  -- TODO: Retire paramTypes if it infers using NULL?
  res = PQexecPrepared(conn, stmtName, nParams, paramValues, NULL, NULL, resultFormat);
  free(values);
  return lean_io_result_mk_ok(to_lean<Result>(res));

alloy c extern "lean_pq_exec_params"
def execParams (connection : @& Connection) (query : String) (nParams : USize) (parameterTypes : ByteArray) (parameterValues : Array String) (parameterLengths : ByteArray) (parameterFormats : ByteArray) (resultFormat : USize) : IO Result :=
  const char *qry = lean_string_cstr(query);
  lean_object** objects = lean_array_cptr(parameterValues);
  PGconn *conn = of_lean<Connection>(connection);
  PGresult *res;
  const uint8_t *paramLengths = lean_sarray_cptr(parameterLengths);
  const uint8_t *paramFormats = lean_sarray_cptr(parameterLengths);
  char **values = (char**)malloc(sizeof(void*)*nParams);
  for (int i = 0; i < nParams; i++) {
    char* current = (char*)lean_string_cstr(objects[i]);
    values[i] = current;
  }
  const char *const *paramValues = (const char *const*)values;
  -- TODO: Retire paramTypes if it infers using NULL?
  res = PQexecParams(conn, qry, nParams, NULL, paramValues, NULL, NULL, resultFormat);
  free(values);
  return lean_io_result_mk_ok(to_lean<Result>(res));

abbrev Response := Except String ResultStatus

def ResultStatus.toString : ResultStatus → String
  | .tuplesOk        => "TuplesOk"
  | .pipelineAborted => "pipelineAborted"
  | .pipelineSync    => "pipelineSync"
  | .singleTuple     => "singleTuple"
  | .copyBoth        => "copyBoth"
  | .fatalError      => "fatalError"
  | .nonfatalError   => "nonfatalError"
  | .badResponse     => "badResponse"
  | .copyIn          => "copyIn"
  | .copyOut         => "copyOut"
  | .commandOk       => "commandOk"
  | .emptyQuery      => "mptyQuery"

def ConnectionStatus.toString: ConnectionStatus → String
  | .ok               => "CONNECTION_OK"
  | .bad              => "CONNECTION_BAD"
  | .started          => "CONNECTION_STARTED"
  | .made             => "CONNECTION_MADE"
  | .awaitingResponse => "CONNECTION_AWAITING_RESPONSE"
  | .authOk           => "CONNECTION_AUTH_OK"
  | .setenv           => "CONNECTION_SETENV"
  | .sslStartup       => "CONNECTION_SSL_STARTUP"
  | .needed           => "CONNECTION_NEEDED"
  | .checkWritable    => "CONNECTION_CHECK_WRITABLE"
  | .consume          => "CONNECTION_CONSUME"
  | .gssStartup       => "CONNECTION_GSS_STARTUP"
  | .checkTarget      => "CONNECTION_CHECK_TARGET"
  | .checkStandby     => "CONNECTION_CHECK_STANDBY"
