import Alloy.C

open scoped Alloy.C

alloy c include <stdlib.h> <string.h> <stdio.h> <stdlib.h> <libpq-fe.h> <lean/lean.h>

namespace LibPQ

alloy c opaque_extern_type Connection => PGconn where
  finalize(ptr) :=
    printf("Cleaning up struct PGconn\n");
    PQfinish(ptr);

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
deriving Inhabited

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
deriving Inhabited

alloy c extern "lean_pq_login"
def login (host : String) (port: String) (dbname: String) (user: String) (password: String) : Connection :=
  const char* hst = lean_string_cstr(host);
  const char* prt = lean_string_cstr(port);
  const char* dbnm = lean_string_cstr(dbname);
  const char* usr = lean_string_cstr(user);
  const char* pwd = lean_string_cstr(password);
  PGconn *conn;
  conn = PQsetdbLogin(hst, prt, NULL, NULL, dbnm, usr, pwd);
  return to_lean<Connection>(conn);

alloy c extern "lean_pq_connection_status"
def connStatus (connection : @& Connection) : ResultStatus :=
  PGresult *res;
  PGconn *conn = of_lean<Connection>(connection);
  ConnStatusType status = PQstatus(conn);
  return of_lean<ConnectionStatus>(status);

alloy c extern "lean_pq_result_status"
def resStatus (result : @& Result) : ResultStatus :=
  PGresult *res;
  res = of_lean<Result>(result);
  ExecStatusType status = PQresultStatus(res);
  return of_lean<ResultStatus>(status);

alloy c extern "lean_pq_get_error_message"
def connErr (connection : @& Connection) : String :=
  PGconn *conn = of_lean<Connection>(connection);
  return lean_mk_string(PQerrorMessage(conn));

alloy c extern "lean_pq_exec"
def exec (connection : @& Connection) (query : String) : Result :=
  PGconn *conn = of_lean<Connection>(connection);
  PGresult *res;
  res = PQexec(conn, lean_string_cstr(query));
  return to_lean<Result>(res);

alloy c extern "lean_pq_prepare"
def prepare (connection : @& Connection) (statementName: String) (query : String) (nParameters : USize) (parameterTypes : ByteArray) : Result :=
  PGconn *conn = of_lean<Connection>(connection);
  const char *stmtName = lean_string_cstr(statementName);
  const char *qry = lean_string_cstr(query);
  int nParams = nParameters;
  const Oid *paramTypes = lean_float_array_cptr(parameterTypes);
  PGresult *res;
  res = PQprepare(conn, stmtName, qry, nParams, paramTypes);
  return to_lean<Result>(res);

alloy c extern "lean_pq_exec_prepared"
def execPrepared (connection : @& Connection) (statementName: String) (nParameters : USize) (parameterValues : Array String) (parameterLengths : ByteArray) (parameterFormats : ByteArray) (resultFormat : USize) : Result :=
  const char *stmtName = lean_string_cstr(statementName);
  lean_object** objects = lean_array_cptr(parameterValues);
  PGconn *conn = of_lean<Connection>(connection);
  PGresult *res;
  const int *paramLengths = lean_float_array_cptr(parameterLengths);
  const int *paramFormats = lean_float_array_cptr(parameterLengths);
  printf("number; %d\n", nParameters);
  char **values = malloc(sizeof(void*)*nParameters);
  for (int i = 0; i < nParameters; i++) {
    char* current = lean_string_cstr(objects[i]);
    values[i] = current;
    printf("%s\n", current);
  }
  res = PQexecPrepared(conn, stmtName, nParameters, values, paramLengths, paramFormats, resultFormat);
  free(values);
  return to_lean<Result>(res);
