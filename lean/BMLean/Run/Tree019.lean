import BMLean.Tables
import BMLean.Data.Tree019

namespace BMC

theorem treeOk_019 : treeChunkOk (parseTrees BMD.tree019) = true := by native_decide

end BMC
