import BMLean.Tables
import BMLean.Data.Hub024

namespace BMC

theorem hubOk_024 : hubChunkOk (parseRows BMD.hub024) = true := by native_decide

end BMC
