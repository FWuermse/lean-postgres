import Lake
open System Lake DSL

package open_onnection where
  dependencies := #[{
    name := `postgres
    src := Source.path "../.."
  }]
