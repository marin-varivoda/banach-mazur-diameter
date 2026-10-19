import BMLean.Tables
import BMLean.Data.Tree020

namespace BMC

theorem treeOk_020 : treeChunkOk (parseTrees BMD.tree020) = true := by native_decide

end BMC
