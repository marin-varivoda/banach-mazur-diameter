import BMLean.Tables
import BMLean.Data.Tree000

namespace BMC

theorem treeOk_000 : treeChunkOk (parseTrees BMD.tree000) = true := by native_decide

end BMC
