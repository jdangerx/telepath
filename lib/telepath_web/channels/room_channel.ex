defmodule TelepathWeb.RoomChannel do
  use Phoenix.Channel
  alias Telepath.State

  def join("room:lobby", _message, socket) do
    send(self(), :after_join)
    user_id = Ecto.UUID.generate
    {:ok, user_id, assign(socket, :user_id, user_id)}
  end
  def join("room:" <> _private_room_id, _params, _socket) do
    {:error, %{reason: "unauthorized"}}
  end

  def handle_info(:after_join, socket) do
    push socket, "init_state", State.get_all()
    {:noreply, socket}
  end

  def handle_in("new_msg", msg, socket) do
    %{"user" => user, "body" => body, "nick" => nick} = msg
    State.put(user, %{"body" => body, "nick" => nick})
    broadcast!(socket, "new_msg", msg)
    {:noreply, socket}
  end

  def terminate(reason, socket) do
    State.delete(socket.assigns.user_id)
    broadcast!(socket, "user_left", %{"user" => socket.assigns.user_id})
    :ok
  end
end
