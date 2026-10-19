import BMLean.Tables
import BMLean.Data.Hub055

namespace BMC

theorem hubOk_055 : hubChunkOk (parseRows BMD.hub055) = true := by native_decide

end BMC
