import BMLean.Tables
import BMLean.Data.Tree017

namespace BMC

theorem treeOk_017 : treeChunkOk (parseTrees BMD.tree017) = true := by native_decide

end BMC
