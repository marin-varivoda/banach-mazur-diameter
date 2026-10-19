import BMLean.Tables
import BMLean.Data.Tree003

namespace BMC

theorem treeOk_003 : treeChunkOk (parseTrees BMD.tree003) = true := by native_decide

end BMC
