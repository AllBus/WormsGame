
var list = new GameListener();

list.onChangeScore = function(score) {
    var scoreView = document.getElementById("score");
    scoreView.textContent = "score "+score;
};

list.onNewGame = function() {
  //  console.log("tag New "+WormApp.isGameOver());
};

list.onGameOver = function() {
  //  console.log("tag Over "+WormApp.isGameOver());
};


list.onPause = function(pause){
  //  console.log("pause "+WormApp.isPause());
};

WormApp.jslistener = list;


