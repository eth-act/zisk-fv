import Lake
open Lake DSL

package «rv64im-aeneas-extraction» {}

require «aeneas» from "./.aeneas-lean"
require «zisk-fv» from "../.."

@[default_target]
lean_lib «Rv64imExtract» {}
