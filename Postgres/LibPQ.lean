/-
  Copyright (c) 2024 Florian Würmseer. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Florian Würmseer
-/

namespace LibPQ

-- Opaque handle wrapping PGconn*
private opaque ConnectionPointed : NonemptyType
def Connection : Type := ConnectionPointed.type
instance : Nonempty Connection := ConnectionPointed.property

-- Opaque handle wrapping PGresult*
private opaque ResultPointed : NonemptyType
def Result : Type := ResultPointed.type
instance : Nonempty Result := ResultPointed.property

structure Context where
  conn : Connection

abbrev SQL := ReaderT Context IO

inductive ConnectionStatus
  | ok
  | bad
  | started
  | made
  | awaitingResponse
  | authOk
  | setenv
  | sslStartup
  | needed
  | checkWritable
  | consume
  | gssStartup
  | checkTarget
  | checkStandby
  deriving Inhabited, BEq

inductive ResultStatus
  | emptyQuery
  | commandOk
  | tuplesOk
  | copyOut
  | copyIn
  | badResponse
  | nonfatalError
  | fatalError
  | copyBoth
  | singleTuple
  | pipelineSync
  | pipelineAborted
  deriving Inhabited, BEq

@[extern "lean_pq_login"]
opaque login (host port dbname user password : String) : IO Connection

@[extern "lean_pq_connect"]
opaque connect (connectionInfo : String) : IO Connection

@[extern "lean_pq_connection_status"]
opaque Connection.status (connection : @& Connection) : ConnectionStatus

@[extern "lean_pq_result_status"]
opaque Result.status (result : @& Result) : ResultStatus

@[extern "lean_pq_get_error_message"]
opaque Connection.error (connection : @& Connection) : IO String

@[extern "lean_pq_fname"]
opaque fname (result : @& Result) (column_number : USize) : IO String

@[extern "lean_pq_get_value"]
opaque getValue (result : @& Result) (row col : USize) : IO String

@[extern "lean_pq_n_tuples"]
opaque nTuples (result : @& Result) : IO USize

@[extern "lean_pq_n_fields"]
opaque nFields (result : @& Result) : IO USize

@[extern "lean_pq_exec"]
opaque exec (connection : @& Connection) (query : String) : IO Result

@[extern "lean_pq_prepare"]
opaque prepare (connection : @& Connection) (statementName query : String)
    (nParams : USize) (parameterTypes : ByteArray) : IO Result

@[extern "lean_pq_exec_prepared"]
opaque execPrepared (connection : @& Connection) (statementName : String)
    (nParams : USize) (parameterValues : Array String)
    (parameterLengths parameterFormats : ByteArray) (resultFormat : USize) : IO Result

@[extern "lean_pq_exec_params"]
opaque execParams (connection : @& Connection) (query : String)
    (nParams : USize) (parameterTypes : ByteArray) (parameterValues : Array String)
    (parameterLengths parameterFormats : ByteArray) (resultFormat : USize) : IO Result

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
  | .emptyQuery      => "emptyQuery"

def ConnectionStatus.toString : ConnectionStatus → String
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

end LibPQ
