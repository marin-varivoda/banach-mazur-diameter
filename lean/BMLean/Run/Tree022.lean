import BMLean.Tables
import BMLean.Data.Tree022

namespace BMC

theorem treeOk_022 : treeChunkOk (parseTrees BMD.tree022) = true := by native_decide

end BMC
