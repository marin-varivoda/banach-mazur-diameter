import BMLean.Tables
import BMLean.Data.Hub007

namespace BMC

theorem hubOk_007 : hubChunkOk (parseRows BMD.hub007) = true := by native_decide

end BMC
