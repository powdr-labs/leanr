-- Root of the `Leanr` library: importing it builds the whole public surface.
-- `Leanr.Optimizer` transitively pulls in the framework and every pipelined pass;
-- the rest are the OpenVM instantiation, the powdr-export parser, and the CLI utilities.
-- A pass intentionally not (yet) in the pipeline should be imported here too, so
-- `lake build` still checks it.
import Leanr.Optimizer
import Leanr.OpenVM.Facts
import Leanr.JsonParser
import Leanr.Utils.Dsl
import Leanr.Utils.Size
