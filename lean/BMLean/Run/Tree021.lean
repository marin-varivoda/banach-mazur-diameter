import BMLean.Tables
import BMLean.Data.Tree021

namespace BMC

theorem treeOk_021 : treeChunkOk (parseTrees BMD.tree021) = true := by native_decide

end BMC
