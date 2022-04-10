import Lake
open System Lake DSL

package query where
  dependencies := #[{
    name := `postgres
    src := Source.path "../.."
  }]
