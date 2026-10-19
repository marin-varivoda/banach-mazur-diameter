import BMLean.Tables
import BMLean.Data.Tree014

namespace BMC

theorem treeOk_014 : treeChunkOk (parseTrees BMD.tree014) = true := by native_decide

end BMC
