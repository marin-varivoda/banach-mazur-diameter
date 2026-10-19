import BMLean.Tables
import BMLean.Data.Hub066

namespace BMC

theorem hubOk_066 : hubChunkOk (parseRows BMD.hub066) = true := by native_decide

end BMC
