import BMLean.Tables
import BMLean.Data.Hub017

namespace BMC

theorem hubOk_017 : hubChunkOk (parseRows BMD.hub017) = true := by native_decide

end BMC
