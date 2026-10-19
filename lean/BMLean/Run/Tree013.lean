import BMLean.Tables
import BMLean.Data.Tree013

namespace BMC

theorem treeOk_013 : treeChunkOk (parseTrees BMD.tree013) = true := by native_decide

end BMC
