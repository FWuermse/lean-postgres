import Lake
open System Lake DSL

package insert where
  dependencies := #[{
    name := `postgres
    src := Source.path "../.."
  }]
