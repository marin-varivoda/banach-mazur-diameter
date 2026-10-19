import BMLean.Tables
import BMLean.Data.Tree001

namespace BMC

theorem treeOk_001 : treeChunkOk (parseTrees BMD.tree001) = true := by native_decide

end BMC
