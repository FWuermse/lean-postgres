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

alloy c extern "lean_pq_login"
def login (host : String) (port: String) (dbname: String) (user: String) (password: String) : Connection :=
  const char* hst = lean_string_cstr(host);
  const char* prt = lean_string_cstr(port);
  const char* dbnm = lean_string_cstr(dbname);
  const char* usr = lean_string_cstr(user);
  const char* pwd = lean_string_cstr(password);
  PGconn *conn;
  conn = PQsetdbLogin(hst, prt, NULL, NULL, dbnm, usr, pwd);
  printf("Return Connection\n");
  return to_lean<Connection>(conn);

alloy c extern "lean_pq_exec"
def exec (connection : @& Connection) (query : String) : IO Result :=
  PGconn *conn = of_lean<Connection>(connection);
  if (PQstatus(conn) != CONNECTION_OK) {
      fprintf(stderr, "Connection to database failed: %s\n", PQerrorMessage(conn));
  }
  PGresult *res;
  res = PQexec(conn, lean_string_cstr(query));
  if (PQresultStatus(res) != PGRES_TUPLES_OK) {
      fprintf(stderr, "Query failed: %s", PQerrorMessage(conn));
  }

  int rows = PQntuples(res);
  printf("Tables in database:\n");
  for (int i = 0; i < rows; i++) {
      printf("%s\n", PQgetvalue(res, i, 0));
  }
  return lean_io_result_mk_ok(to_lean<Result>(res));
