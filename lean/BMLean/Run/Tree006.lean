import BMLean.Tables
import BMLean.Data.Tree006

namespace BMC

theorem treeOk_006 : treeChunkOk (parseTrees BMD.tree006) = true := by native_decide

end BMC
