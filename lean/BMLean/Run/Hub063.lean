import BMLean.Tables
import BMLean.Data.Hub063

namespace BMC

theorem hubOk_063 : hubChunkOk (parseRows BMD.hub063) = true := by native_decide

end BMC
