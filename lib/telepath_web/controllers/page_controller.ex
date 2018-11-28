defmodule TelepathWeb.PageController do
  use TelepathWeb, :controller

  def index(conn, _params) do
    render(conn, "index.html")
  end
end
