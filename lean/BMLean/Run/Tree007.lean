import BMLean.Tables
import BMLean.Data.Tree007

namespace BMC

theorem treeOk_007 : treeChunkOk (parseTrees BMD.tree007) = true := by native_decide

end BMC
