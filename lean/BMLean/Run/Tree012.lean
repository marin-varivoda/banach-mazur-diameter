import BMLean.Tables
import BMLean.Data.Tree012

namespace BMC

theorem treeOk_012 : treeChunkOk (parseTrees BMD.tree012) = true := by native_decide

end BMC
