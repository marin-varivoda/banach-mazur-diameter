import BMLean.Tables
import BMLean.Data.Tree008

namespace BMC

theorem treeOk_008 : treeChunkOk (parseTrees BMD.tree008) = true := by native_decide

end BMC
