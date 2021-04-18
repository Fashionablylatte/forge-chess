d3.selectAll("svg > *").remove();

const BOARD_SIZE = 5;
const OFFSET = 50;

function printValue(row, col, xoffset, yoffset, value) {
    switch(value) {
      case "BN0":
      case "BN1":
        var myimage = d3.select(svg).append('image')
          .attr('xlink:href', 'https://srv2.imgonline.com.ua/result_img/imgonline-com-ua-cut-image-MQ3ZfwleMfk/image_part_010.png')
          .attr("x", row*75 + xoffset)
          .attr("y", col*75 + yoffset)
          .attr('width', 50)
          .attr('height', 50);
         break;
      case "WN0":
      case "WN1":
        var myimage = d3.select(svg).append('image')
          .attr('xlink:href', 'https://srv2.imgonline.com.ua/result_img/imgonline-com-ua-cut-image-MQ3ZfwleMfk/image_part_004.png')
          .attr("x", row*75 + xoffset)
          .attr("y", col*75 + yoffset)
          .attr('width', 50)
          .attr('height', 50);
         break;
      case "WR0":
      case "WR1":
        var myimage = d3.select(svg).append('image')
          .attr('xlink:href', 'https://srv2.imgonline.com.ua/result_img/imgonline-com-ua-cut-image-MQ3ZfwleMfk/image_part_005.png')
          .attr("x", row*70 + xoffset)
          .attr("y", col*65 + yoffset)
          .attr('width', 50)
          .attr('height', 50);
         break;
      case "BR0":
      case "BR1":
        var myimage = d3.select(svg).append('image')
          .attr('xlink:href', 'https://srv2.imgonline.com.ua/result_img/imgonline-com-ua-cut-image-MQ3ZfwleMfk/image_part_011.png')
          .attr("x", row*70 + xoffset)
          .attr("y", col*65 + yoffset)
          .attr('width', 50)
          .attr('height', 50);
         break;
      case "BB0":
      case "BB1":
        var myimage = d3.select(svg).append('image')
          .attr('xlink:href', 'https://srv2.imgonline.com.ua/result_img/imgonline-com-ua-cut-image-MQ3ZfwleMfk/image_part_009.png')
          .attr("x", row*75 + xoffset)
          .attr("y", col*75 + yoffset)
          .attr('width', 50)
          .attr('height', 50);
         break;
      case "WB0":
      case "WB1":
        var myimage = d3.select(svg).append('image')
          .attr('xlink:href', 'https://srv2.imgonline.com.ua/result_img/imgonline-com-ua-cut-image-MQ3ZfwleMfk/image_part_003.png')
          .attr("x", row*60 + xoffset)
          .attr("y", col*60 + yoffset)
          .attr('width', 50)
          .attr('height', 50);
         break;
      case "WQ0":
      case "WQ1":
        var myimage = d3.select(svg).append('image')
          .attr('xlink:href', 'https://srv2.imgonline.com.ua/result_img/imgonline-com-ua-cut-image-MQ3ZfwleMfk/image_part_002.png')
          .attr("x", row*60 + xoffset)
          .attr("y", col*60 + yoffset)
          .attr('width', 50)
          .attr('height', 50);
         break;
      case "BQ0":
      case "BQ1":
        var myimage = d3.select(svg).append('image')
          .attr('xlink:href', 'https://srv2.imgonline.com.ua/result_img/imgonline-com-ua-cut-image-MQ3ZfwleMfk/image_part_002.png')
          .attr("x", row*60 + xoffset)
          .attr("y", col*60 + yoffset)
          .attr('width', 50)
          .attr('height', 50);
         break;
      case "WK0":
      case "WK1":
        var myimage = d3.select(svg).append('image')
          .attr('xlink:href', 'https://srv2.imgonline.com.ua/result_img/imgonline-com-ua-cut-image-MQ3ZfwleMfk/image_part_001.png')
          .attr("x", row*60 + xoffset)
          .attr("y", col*65 + yoffset)
          .attr('width', 50)
          .attr('height', 50);
         break;
      case "BK0":
      case "BK1":
        var myimage = d3.select(svg).append('image')
          .attr('xlink:href', 'https://srv2.imgonline.com.ua/result_img/imgonline-com-ua-cut-image-MQ3ZfwleMfk/image_part_007.png')
          .attr("x", row*60 + xoffset)
          .attr("y", col*65 + yoffset)
          .attr('width', 50)
          .attr('height', 50);
         break;
      case "WP0":
      case "WP1":
        var myimage = d3.select(svg).append('image')
          .attr('xlink:href', 'https://srv2.imgonline.com.ua/result_img/imgonline-com-ua-cut-image-MQ3ZfwleMfk/image_part_006.png')
          .attr("x", row*70 + xoffset)
          .attr("y", col*60 + yoffset)
          .attr('width', 50)
          .attr('height', 50);
         break;
      case "BP0":
      case "BP1":
        var myimage = d3.select(svg).append('image')
          .attr('xlink:href', 'https://srv2.imgonline.com.ua/result_img/imgonline-com-ua-cut-image-MQ3ZfwleMfk/image_part_012.png')
          .attr("x", row*70 + xoffset)
          .attr("y", col*60 + yoffset)
          .attr('width', 50)
          .attr('height', 50);
         break;
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

function convert(square) {
  const precontent = square.join(pc)
  let content = ''
  if ((Black0.pieces).join(precontent).empty()) {
    content = 'W' + precontent.toString()
  } else {
    content = 'B' + precontent.toString()
  }
  if (precontent.empty()) {
    return '-'
  } else {
    return content.toString()
  }
}

function toCoord(rc) {
  return rc.charAt(3);
}

function printBoard(startRow, startCol) {
  let row = startRow;
  let col = startCol;
  
  for (r = 0; r < BOARD_SIZE; r++) {
    printValue(0, r, OFFSET, OFFSET, toCoord(row.toString()));
    for (c = 1; c < BOARD_SIZE + 1; c++) {
      const square = coord.join(col).join(row)
      printValue(c, r, OFFSET, OFFSET, convert(square));
      col = col.c_next;
    }
    col = startCol;
    row = row.r_prev;
  }
  
  for (c = 1; c < BOARD_SIZE + 1; c++) {
    printValue(c, BOARD_SIZE, OFFSET, OFFSET, toCoord(col.toString()));
    col = col.c_next;
  }
  
}
printBoard(row5, colA)
