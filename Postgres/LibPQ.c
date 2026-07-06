/*
  Copyright (c) 2024 Florian Würmseer. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Florian Würmseer
*/

#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <libpq-fe.h>
#include <lean/lean.h>

/* ---- Connection opaque type -------------------------------------------- */

static void noop_foreach(void *ptr, b_lean_obj_arg f) { (void)ptr; (void)f; }

static void lean_pq_connection_finalize(void *ptr) {
    PQfinish((PGconn *)ptr);
}

static lean_external_class *lean_pq_connection_class = NULL;

static lean_external_class *get_connection_class(void) {
    if (lean_pq_connection_class == NULL)
        lean_pq_connection_class = lean_register_external_class(
            lean_pq_connection_finalize, noop_foreach);
    return lean_pq_connection_class;
}

static inline lean_obj_res connection_to_lean(PGconn *conn) {
    return lean_alloc_external(get_connection_class(), conn);
}

static inline PGconn *connection_of_lean(lean_obj_arg o) {
    return (PGconn *)lean_get_external_data(o);
}

/* ---- Result opaque type ------------------------------------------------- */

static void lean_pq_result_finalize(void *ptr) {
    PQclear((PGresult *)ptr);
}

static lean_external_class *lean_pq_result_class = NULL;

static lean_external_class *get_result_class(void) {
    if (lean_pq_result_class == NULL)
        lean_pq_result_class = lean_register_external_class(
            lean_pq_result_finalize, noop_foreach);
    return lean_pq_result_class;
}

static inline lean_obj_res result_to_lean(PGresult *res) {
    return lean_alloc_external(get_result_class(), res);
}

static inline PGresult *result_of_lean(lean_obj_arg o) {
    return (PGresult *)lean_get_external_data(o);
}

/* ---- ConnectionStatus enum (must match Lean inductive order) ------------ */
/* Lean inductive tags are assigned 0, 1, 2, ... in declaration order.
   Order: ok bad started made awaitingResponse authOk setenv sslStartup
          needed checkWritable consume gssStartup checkTarget checkStandby */

static uint8_t conn_status_to_lean(ConnStatusType s) {
    switch (s) {
        case CONNECTION_OK:               return 0;
        case CONNECTION_BAD:              return 1;
        case CONNECTION_STARTED:          return 2;
        case CONNECTION_MADE:             return 3;
        case CONNECTION_AWAITING_RESPONSE: return 4;
        case CONNECTION_AUTH_OK:          return 5;
        case CONNECTION_SETENV:           return 6;
        case CONNECTION_SSL_STARTUP:      return 7;
        case CONNECTION_NEEDED:           return 8;
        case CONNECTION_CHECK_WRITABLE:   return 9;
        case CONNECTION_CONSUME:          return 10;
        case CONNECTION_GSS_STARTUP:      return 11;
        case CONNECTION_CHECK_TARGET:     return 12;
        case CONNECTION_CHECK_STANDBY:    return 13;
        default:                          return 1; /* bad */
    }
}

/* ---- ResultStatus enum (must match Lean inductive order) --------------- */
/* Order: emptyQuery commandOk tuplesOk copyOut copyIn badResponse
          nonfatalError fatalError copyBoth singleTuple pipelineSync pipelineAborted */

static uint8_t result_status_to_lean(ExecStatusType s) {
    switch (s) {
        case PGRES_EMPTY_QUERY:     return 0;
        case PGRES_COMMAND_OK:      return 1;
        case PGRES_TUPLES_OK:       return 2;
        case PGRES_COPY_OUT:        return 3;
        case PGRES_COPY_IN:         return 4;
        case PGRES_BAD_RESPONSE:    return 5;
        case PGRES_NONFATAL_ERROR:  return 6;
        case PGRES_FATAL_ERROR:     return 7;
        case PGRES_COPY_BOTH:       return 8;
        case PGRES_SINGLE_TUPLE:    return 9;
        case PGRES_PIPELINE_SYNC:   return 10;
        case PGRES_PIPELINE_ABORTED: return 11;
        default:                    return 7; /* fatalError */
    }
}

/* ---- Public FFI functions ----------------------------------------------- */

LEAN_EXPORT lean_obj_res lean_pq_login(
        lean_obj_arg host, lean_obj_arg port, lean_obj_arg dbname,
        lean_obj_arg user, lean_obj_arg password, lean_obj_arg world) {
    PGconn *conn = PQsetdbLogin(
        lean_string_cstr(host), lean_string_cstr(port),
        NULL, NULL,
        lean_string_cstr(dbname),
        lean_string_cstr(user), lean_string_cstr(password));
    lean_dec(host); lean_dec(port); lean_dec(dbname);
    lean_dec(user); lean_dec(password);
    return lean_io_result_mk_ok(connection_to_lean(conn));
}

LEAN_EXPORT lean_obj_res lean_pq_connect(lean_obj_arg conninfo, lean_obj_arg world) {
    PGconn *conn = PQconnectdb(lean_string_cstr(conninfo));
    lean_dec(conninfo);
    return lean_io_result_mk_ok(connection_to_lean(conn));
}

LEAN_EXPORT lean_obj_res lean_pq_connection_status(lean_obj_arg connection) {
    PGconn *conn = connection_of_lean(connection);
    return lean_box(conn_status_to_lean(PQstatus(conn)));
}

LEAN_EXPORT lean_obj_res lean_pq_result_status(lean_obj_arg result) {
    PGresult *res = result_of_lean(result);
    return lean_box(result_status_to_lean(PQresultStatus(res)));
}

LEAN_EXPORT lean_obj_res lean_pq_get_error_message(lean_obj_arg connection, lean_obj_arg world) {
    PGconn *conn = connection_of_lean(connection);
    return lean_io_result_mk_ok(lean_mk_string(PQerrorMessage(conn)));
}

LEAN_EXPORT lean_obj_res lean_pq_fname(lean_obj_arg result, size_t column_number, lean_obj_arg world) {
    PGresult *res = result_of_lean(result);
    return lean_io_result_mk_ok(lean_mk_string(PQfname(res, (int)column_number)));
}

LEAN_EXPORT lean_obj_res lean_pq_get_value(lean_obj_arg result, size_t row, size_t col, lean_obj_arg world) {
    PGresult *res = result_of_lean(result);
    return lean_io_result_mk_ok(lean_mk_string(PQgetvalue(res, (int)row, (int)col)));
}

LEAN_EXPORT lean_obj_res lean_pq_n_tuples(lean_obj_arg result, lean_obj_arg world) {
    PGresult *res = result_of_lean(result);
    return lean_io_result_mk_ok(lean_box_usize((size_t)PQntuples(res)));
}

LEAN_EXPORT lean_obj_res lean_pq_n_fields(lean_obj_arg result, lean_obj_arg world) {
    PGresult *res = result_of_lean(result);
    return lean_io_result_mk_ok(lean_box_usize((size_t)PQnfields(res)));
}

LEAN_EXPORT lean_obj_res lean_pq_exec(lean_obj_arg connection, lean_obj_arg query, lean_obj_arg world) {
    PGconn *conn = connection_of_lean(connection);
    PGresult *res = PQexec(conn, lean_string_cstr(query));
    lean_dec(query);
    return lean_io_result_mk_ok(result_to_lean(res));
}

LEAN_EXPORT lean_obj_res lean_pq_prepare(
        lean_obj_arg connection, lean_obj_arg stmtName,
        lean_obj_arg query, size_t nParams,
        lean_obj_arg paramTypes, lean_obj_arg world) {
    PGconn *conn = connection_of_lean(connection);
    PGresult *res = PQprepare(conn,
        lean_string_cstr(stmtName), lean_string_cstr(query),
        (int)nParams, NULL);
    lean_dec(stmtName); lean_dec(query); lean_dec(paramTypes);
    return lean_io_result_mk_ok(result_to_lean(res));
}

LEAN_EXPORT lean_obj_res lean_pq_exec_prepared(
        lean_obj_arg connection, lean_obj_arg stmtName,
        size_t nParams, lean_obj_arg paramValues,
        lean_obj_arg paramLengths, lean_obj_arg paramFormats,
        size_t resultFormat, lean_obj_arg world) {
    PGconn *conn = connection_of_lean(connection);
    lean_object **objects = lean_array_cptr(paramValues);
    char **values = (char **)malloc(sizeof(char *) * nParams);
    for (size_t i = 0; i < nParams; i++)
        values[i] = (char *)lean_string_cstr(objects[i]);
    PGresult *res = PQexecPrepared(conn,
        lean_string_cstr(stmtName), (int)nParams,
        (const char *const *)values, NULL, NULL, (int)resultFormat);
    free(values);
    lean_dec(stmtName); lean_dec(paramValues);
    lean_dec(paramLengths); lean_dec(paramFormats);
    return lean_io_result_mk_ok(result_to_lean(res));
}

LEAN_EXPORT lean_obj_res lean_pq_exec_params(
        lean_obj_arg connection, lean_obj_arg query,
        size_t nParams, lean_obj_arg paramTypes,
        lean_obj_arg paramValues,
        lean_obj_arg paramLengths, lean_obj_arg paramFormats,
        size_t resultFormat, lean_obj_arg world) {
    PGconn *conn = connection_of_lean(connection);
    lean_object **objects = lean_array_cptr(paramValues);
    char **values = (char **)malloc(sizeof(char *) * nParams);
    for (size_t i = 0; i < nParams; i++)
        values[i] = (char *)lean_string_cstr(objects[i]);
    PGresult *res = PQexecParams(conn, lean_string_cstr(query),
        (int)nParams, NULL,
        (const char *const *)values, NULL, NULL, (int)resultFormat);
    free(values);
    lean_dec(query); lean_dec(paramTypes);
    lean_dec(paramValues); lean_dec(paramLengths); lean_dec(paramFormats);
    return lean_io_result_mk_ok(result_to_lean(res));
}
