import BMLean.Tables
import BMLean.Data.Hub045

namespace BMC

theorem hubOk_045 : hubChunkOk (parseRows BMD.hub045) = true := by native_decide

end BMC
