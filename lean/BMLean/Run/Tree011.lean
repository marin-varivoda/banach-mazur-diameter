import BMLean.Tables
import BMLean.Data.Tree011

namespace BMC

theorem treeOk_011 : treeChunkOk (parseTrees BMD.tree011) = true := by native_decide

end BMC
