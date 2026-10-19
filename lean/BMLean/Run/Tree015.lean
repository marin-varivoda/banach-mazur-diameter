import BMLean.Tables
import BMLean.Data.Tree015

namespace BMC

theorem treeOk_015 : treeChunkOk (parseTrees BMD.tree015) = true := by native_decide

end BMC
