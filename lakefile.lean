import Lake
open System Lake DSL

package postgres where
  dependencies := #[{
    name := `socket
    src := Source.git "https://github.com/xubaiw/lean4-socket.git" "main"
  }]
