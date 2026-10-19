import BMLean.Tables
import BMLean.Data.Hub034

namespace BMC

theorem hubOk_034 : hubChunkOk (parseRows BMD.hub034) = true := by native_decide

end BMC
