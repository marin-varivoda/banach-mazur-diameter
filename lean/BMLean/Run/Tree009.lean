import BMLean.Tables
import BMLean.Data.Tree009

namespace BMC

theorem treeOk_009 : treeChunkOk (parseTrees BMD.tree009) = true := by native_decide

end BMC
