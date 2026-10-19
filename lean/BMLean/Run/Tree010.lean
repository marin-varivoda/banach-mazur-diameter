import BMLean.Tables
import BMLean.Data.Tree010

namespace BMC

theorem treeOk_010 : treeChunkOk (parseTrees BMD.tree010) = true := by native_decide

end BMC
