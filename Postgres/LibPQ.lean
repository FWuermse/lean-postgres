import Alloy.C

open scoped Alloy.C

alloy c section

#include <lean/lean.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <libpq-fe.h>

end

namespace LibPQ

alloy c opaque_extern_type PGconn => struct pgconn_wrapper where
  finalize(ptr) :=
    struct pgconn_wrapper* conn = (struct pgconn_wrapper*)ptr;
    printf("Cleaning up struct PGconn\n");
    // fails on: ld64.lld: error: undefined symbol: _PQfinish
    // PQfinish(conn);

alloy c extern "lean_pq_connect"
def connect (host : String) (port: String) (dbname: String) (user: String) (password: String) : IO PGconn :=
  printf("Hello World\n");
  PGconn *conn;
  // fails on: ld64.lld: error: undefined symbol: _PQsetdbLogin
  // conn = PQsetdbLogin(host, port, NULL, NULL, dbname, user, password);
  return lean_io_result_mk_ok(to_lean<PGconn>(conn));;
