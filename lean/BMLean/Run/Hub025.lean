import BMLean.Tables
import BMLean.Data.Hub025

namespace BMC

theorem hubOk_025 : hubChunkOk (parseRows BMD.hub025) = true := by native_decide

end BMC
