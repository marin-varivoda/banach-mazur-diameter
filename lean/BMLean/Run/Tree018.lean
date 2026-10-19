import BMLean.Tables
import BMLean.Data.Tree018

namespace BMC

theorem treeOk_018 : treeChunkOk (parseTrees BMD.tree018) = true := by native_decide

end BMC
