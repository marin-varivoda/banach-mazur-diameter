import BMLean.Tables
import BMLean.Data.Hub026

namespace BMC

theorem hubOk_026 : hubChunkOk (parseRows BMD.hub026) = true := by native_decide

end BMC
