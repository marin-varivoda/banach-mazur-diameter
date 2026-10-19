import BMLean.Tables
import BMLean.Data.Tree016

namespace BMC

theorem treeOk_016 : treeChunkOk (parseTrees BMD.tree016) = true := by native_decide

end BMC
