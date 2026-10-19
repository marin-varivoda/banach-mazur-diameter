import BMLean.Tables
import BMLean.Data.Tree005

namespace BMC

theorem treeOk_005 : treeChunkOk (parseTrees BMD.tree005) = true := by native_decide

end BMC
