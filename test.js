d3.selectAll("svg > *").remove();

const BOARD_SIZE = 5;
const OFFSET = 50;

function make_piece(url) {
  const img = document.createElement("img")
  img.src = url
  img.style.width = '100%'
  img.style.height = '15%'
  img.style.display = 'block'
  img.style['margin-bottom'] = '10%'
  
  return img;
}

function printValue(row, col, xoffset, yoffset, value) {
    switch(value) {
//       case "BN0":
//         var myimage = d3.select(svg).append('image')
//           .attr('xlink:href', 'http://clipart-library.com/images/8TGKgnpTa.png')
//           .attr("x", row*75 + xoffset*1)
//           .attr("y", col*75 + yoffset*1)
//           .attr('width', 50)
//           .attr('height', 50);
//          break;
//       case "WN0":
//         var myimage = d3.select(svg).append('image')
//           .attr('xlink:href', 'http://clipart-library.com/images/pio5AeRaT.jpg')
//           .attr("x", row*75 + xoffset*1)
//           .attr("y", col*75 + yoffset*1)
//           .attr('width', 50)
//           .attr('height', 50);
//          break;
//       case "WR0":
//         var myimage = d3.select(svg).append('image')
//           .attr('xlink:href', 'http://clipart-library.com/images/8cxXrazcp.jpg')
//           .attr("x", row*66 + xoffset*1)
//           .attr("y", col*60 + yoffset*1)
//           .attr('width', 50)
//           .attr('height', 50);
//          break;
//       case "BB0":
//         var myimage = d3.select(svg).append('image')
//           .attr('xlink:href', 'https://www.pinclipart.com/picdir/big/100-1006999_clipart-silhouette-chess-piece-remix-bishop-alfil-chess.png')
//           .attr("x", row*60 + xoffset*1)
//           .attr("y", col*60 + yoffset*1)
//           .attr('width', 50)
//           .attr('height', 50);
//          break;
//       case "BQ0":
//         var myimage = d3.select(svg).append('image')
//           .attr('xlink:href', 'https://www.clipartmax.com/png/full/204-2042941_clipart-queen-chess-piece-vector.png')
//           .attr("x", row*60 + xoffset*1)
//           .attr("y", col*60 + yoffset*1)
//           .attr('width', 50)
//           .attr('height', 50);
//          break;
//       case "BK0":
//         var myimage = d3.select(svg).append('image')
//           .attr('xlink:href', 'http://clipart-library.com/img/1985567.png')
//           .attr("x", row*58 + xoffset*1)
//           .attr("y", col*65 + yoffset*1)
//           .attr('width', row*40)
//           .attr('height', 50);
//          break; 
      default:
          d3.select(svg)
            .append("text")
            .style("fill", "black")
            .attr("x", row*75 + xoffset)
            .attr("y", col*75 + yoffset)
            .attr("font-size", "xx-large")
            .text(value);
  }
}

// function convert(square) {
//   const squareContent = square.pc.toString()
//   if(squareContent == '') {
//     return '_'
//   } else {
//     return squareContent
//   }
// }

function convert(square) {
  const content = square.join(pc)
  if (content.empty()) {
    return '_'
  } else {
    console.log(content.toString())
    return content.toString()
  }
}

function toCoord(rc) {
  return rc.charAt(3);
}

// printValue(row1, colA, 5, 25, Board0.places[row1][colA])

function printBoard(startRow, startCol) {
  let row = startRow;
  let col = startCol;
  
  for (r = 0; r < BOARD_SIZE; r++) {
    printValue(0, r, OFFSET, OFFSET, toCoord(row.toString()));
    for (c = 1; c < BOARD_SIZE + 1; c++) {
     
      const square = coord.join(col).join(row)
      printValue(c, r, OFFSET, OFFSET, convert(square));
//       printValue(c, r, 50, 50, square.coord.toString())
//       console.log(convert(square));
      col = col.c_next;
    }
    col = startCol;
    row = row.r_prev;
  }
  
  for (c = 1; c < BOARD_SIZE + 1; c++){
    printValue(c, BOARD_SIZE, OFFSET, OFFSET, toCoord(col.toString()));
    col = col.c_next;
  }
  
}

printBoard(row5, colA)


