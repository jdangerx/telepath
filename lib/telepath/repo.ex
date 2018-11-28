defmodule Telepath.Repo do
  use Ecto.Repo,
    otp_app: :telepath,
    adapter: Ecto.Adapters.Postgres
end
