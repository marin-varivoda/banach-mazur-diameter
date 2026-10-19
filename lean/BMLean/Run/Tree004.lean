import BMLean.Tables
import BMLean.Data.Tree004

namespace BMC

theorem treeOk_004 : treeChunkOk (parseTrees BMD.tree004) = true := by native_decide

end BMC
