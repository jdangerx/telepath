defmodule TelepathWeb.RoomChannel do
  use Phoenix.Channel

  def join("room:lobby", _message, socket) do
    {:ok, socket}
  end
  def join("room:" <> _private_room_id, _params, _socket) do
    {:error, %{reason: "unauthorized"}}
  end

  def handle_in("new_msg", msg, socket) do
    broadcast!(socket, "new_msg", msg)
    {:noreply, socket}
  end
end
