import BMLean.Tables
import BMLean.Data.Hub057

namespace BMC

theorem hubOk_057 : hubChunkOk (parseRows BMD.hub057) = true := by native_decide

end BMC
