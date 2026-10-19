import BMLean.Tables
import BMLean.Data.Tree002

namespace BMC

theorem treeOk_002 : treeChunkOk (parseTrees BMD.tree002) = true := by native_decide

end BMC
