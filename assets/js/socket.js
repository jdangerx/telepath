// NOTE: The contents of this file will only be executed if
// you uncomment its entry in "assets/js/app.js".

// To use Phoenix channels, the first step is to import Socket,
// and connect at the socket path in "lib/web/endpoint.ex".
//
// Pass the token on params as below. Or remove it
// from the params if you are not using authentication.
import {Socket} from "phoenix"

let socket = new Socket("/socket", {params: {token: window.userToken}})

socket.connect()

let channel = socket.channel("room:lobby", {})

let chatUsername = document.querySelector("#chat-username");
let chatInput = document.querySelector("#chat-input");
let messagesContainer = document.querySelector("#messages");
let speechBubbles = document.querySelector("#speech-bubbles");

let allUserState = {};

function makeSpeechBubble(username, message) {
  var usernameText = document.createTextNode(username);
  var usernameDiv = document.createElement("div");
  usernameDiv.appendChild(usernameText);
  usernameDiv.className = "speech-bubble-username";
  var messageText = document.createTextNode(message);
  var messageDiv = document.createElement("div");
  messageDiv.appendChild(messageText);
  messageDiv.className = "speech-bubble-message";
  var topDiv = document.createElement("div");
  topDiv.className = "speech-bubble flex-container";
  topDiv.appendChild(usernameDiv);
  topDiv.appendChild(messageDiv);
  return topDiv;
}

function updateSpeechBubbles(state) {
  while (speechBubbles.firstChild) {
    speechBubbles.removeChild(speechBubbles.firstChild);
  }
  speechBubbles.appendChild(makeSpeechBubble("User", "Message"));
  for (var user in state) {
    var bubble = makeSpeechBubble(user, state[user]);
    speechBubbles.appendChild(bubble);
    console.log('appending for user ' + user);
  }
}

chatInput.addEventListener("input", (event) => {
  channel.push("new_msg", {body: chatInput.value, user: chatUsername.value});
});

channel.on("new_msg", (payload) => {
  allUserState[payload.user] = payload.body;
  console.log(payload);
  messagesContainer.innerText = JSON.stringify(allUserState);
  updateSpeechBubbles(allUserState);
});

channel.join()
  .receive("ok", resp => { console.log("Joined successfully", resp) })
  .receive("error", resp => { console.log("Unable to join", resp) })

export default socket
