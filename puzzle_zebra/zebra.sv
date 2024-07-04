//    There are five houses.
//    The Englishman lives in the red house.
//    The Spaniard owns the dog.
//    Coffee is drunk in the green house.
//    The Ukrainian drinks tea.
//    The green house is immediately to the right of the ivory house.
//    The Old Gold smoker owns snails.
//    Kools are smoked in the yellow house.
//    Milk is drunk in the middle house.
//    The Norwegian lives in the first house.
//    The man who smokes Chesterfields lives in the house next to the man with the fox.
//    Kools are smoked in the house next to the house where the horse is kept.
//    The Lucky Strike smoker drinks orange juice.
//    The Japanese smokes Parliaments.
//    The Norwegian lives next to the blue house.



// key:
// 1  English       Red       Dog       Coffee    Oldgold
// 2  Spain         Green     Snail     Tea       Kools
// 3  Ukrain        Ivory     Fox       Milk      Chesterfield
// 4  Norway        Yellow    Horse     Orange    Lucky
// 5  Japan         Blue      Zebra     Water     Parliament

typedef enum logic [2:0] {
        english = 3'd0,
        spain = 3'd1,
        ukrain = 3'd2,
        norway = 3'd3,
        japan = 3'd4
    } nation_key;

typedef enum logic [2:0] {
        red = 3'd0,
        green = 3'd1,
        ivory = 3'd2,
        yellow = 3'd3,
        blue = 3'd4
    } color_key;

typedef enum logic [2:0] {
        dog = 3'd0,
        snail = 3'd1,
        fox = 3'd2,
        horse = 3'd3,
        zebra = 3'd4
    } pet_key;

typedef enum logic [2:0] {
        coffee = 3'd0,
        tea = 3'd1,
        milk = 3'd2,
        juice = 3'd3,
        water = 3'd4
    } drink_key;

typedef enum logic [2:0] {
        oldgold = 3'd0,
        kools = 3'd1,
        chesterfield = 3'd2,
        lucky = 3'd3,
        parliament = 3'd4
    } cigg_key;

module zebra (
    input clk,
    input nation_key nation [4:0],
    input color_key color [4:0],
    input pet_key pet [4:0],
    input drink_key drink [4:0],
    input cigg_key cigg [4:0]
  );




genvar i,j;


//assume all the values for all the grids are from keys
generate
for(i = 0; i < 5; i = i + 1) begin
  always @ (posedge clk) begin
    assume(nation[i] == english || nation[i] == spain || nation[i] == ukrain || nation[i] == norway || nation[i] == japan);
    assume(color[i] == red || color[i] == green || color[i] == ivory || color[i] == yellow || color[i] == blue);
    assume(pet[i] == dog || pet[i] == snail || pet[i] == fox || pet[i] == horse || pet[i] == zebra);
    assume(drink[i] == coffee || drink[i] == tea || drink[i] == milk || drink[i] == juice || drink[i] == water);
    assume(cigg[i] == oldgold || cigg[i] == kools || cigg[i] == chesterfield || cigg[i] == lucky || cigg[i] == parliament);
  end
end
endgenerate

//generate
//for(i = 0; i < 5; i = i + 1) begin
//  always @ (posedge clk) begin
//    assume(nation[i] >= 3'd0);
//    assume(nation[i] <= 3'd4);
//    assume(color[i] >= 3'd0);
//    assume(color[i] <= 3'd4);
//    assume(pet[i] >= 3'd0);
//    assume(pet[i] <= 3'd4);
//    assume(drink[i] >= 3'd0);
//    assume(drink[i] <= 3'd4);
//    assume(cigg[i] >= 3'd0);
//    assume(cigg[i] <= 3'd4);
//  end
//end
//endgenerate

// assume all digits in a column are all different
generate
    for(i = 0; i < 5; i = i + 1) begin
        for(j = i+1; j < 5; j = j + 1) begin
          always @(posedge clk) begin
            assume(nation[i] != nation[j]);
            assume(color[i] != color[j]);
            assume(pet[i] != pet[j]);
            assume(drink[i] != drink[j]);
            assume(cigg[i] != cigg[j]);
          end
        end
     end
endgenerate

`ifdef FORMAL
`ifdef VERIFIC
    
//english in red house
    generate 
       for(i = 0; i < 5; i = i + 1) begin
         english_red: assume property (@(posedge clk) 
            (nation[i] == english) |-> (color[i] == red));
       end
    endgenerate

// spain has dog    
    generate 
       for(i = 0; i < 5; i = i + 1) begin
         spain_dog: assume property (@(posedge clk) 
            (nation[i] == spain) |-> (pet[i] == dog));
       end
    endgenerate

// coffee in green     
    generate 
       for(i = 0; i < 5; i = i + 1) begin
         coffee_green: assume property (@(posedge clk) 
            (drink[i] == coffee) |-> (color[i] == green));
       end
    endgenerate

// ukrain drinks tea
    generate 
       for(i = 0; i < 5; i = i + 1) begin
         ukrain_tea: assume property (@(posedge clk) 
            (nation[i] == ukrain) |-> (drink[i] == tea));
       end
    endgenerate

// green house is right of ivory
    generate 
       for(i = 0; i < 4; i = i + 1) begin
         green_right_ivory: assume property (@(posedge clk) 
            (color[i] == ivory) |-> (color[i+1] == green));
       end
    endgenerate

         ivory_not_5: assume property (@(posedge clk) 
            (color[4] != ivory));
   
// old gold smoker has snail
    generate 
       for(i = 0; i < 5; i = i + 1) begin
         oldgold_snail: assume property (@(posedge clk) 
            (cigg[i] == oldgold) |-> (pet[i] == snail));
       end
    endgenerate

// kools in yellow house
    generate 
       for(i = 0; i < 5; i = i + 1) begin
         kool_yellow: assume property (@(posedge clk) 
            (cigg[i] == kools) |-> (color[i] == yellow));
       end
    endgenerate

// milk is middle
    milk_middle: assume property (@(posedge clk) 
       (drink[2] == milk));
       

// norway in the first house
    norway_first: assume property (@(posedge clk) 
       (nation[0] == norway));

//chesterfield next to fox
 
    chester_0_next_fox: assume property (@(posedge clk) 
       cigg[0] == chesterfield |-> pet[1] == fox);

    chester_4_next_fox: assume property (@(posedge clk) 
       cigg[4] == chesterfield |-> pet[3] == fox);

    generate 
       for(i = 1; i < 4; i = i + 1) begin
         chester_next_fox: assume property (@(posedge clk) 
            (cigg[i] == chesterfield) |-> ((pet[i+1] == fox) || (pet[i-1] == fox)));
       end
    endgenerate


// kools next to horse
    kools_0_next_horse: assume property (@(posedge clk) 
       cigg[0] == kools |-> pet[1] == horse);

    kools_4_next_horse: assume property (@(posedge clk) 
       cigg[4] == kools |-> pet[3] == horse);
    
    generate 
       for(i = 1; i < 4; i = i + 1) begin
         kools_next_horse: assume property (@(posedge clk) 
            (cigg[i] == kools) |-> ((pet[i+1] == horse) || (pet[i-1] == horse)));
       end
    endgenerate

//lucky strik orange juice
    generate 
       for(i = 0; i < 5; i = i + 1) begin
         lucky_orange: assume property (@(posedge clk) 
            (cigg[i] == lucky) |-> (drink[i] == juice));
       end
    endgenerate

//japan parliament
    generate 
       for(i = 0; i < 5; i = i + 1) begin
         japan_parliament: assume property (@(posedge clk) 
            (nation[i] == japan) |-> (cigg[i] == parliament));
       end
    endgenerate

// norway next to blue
//         norway_next_blue: assume property (@(posedge clk) 
//            (zebra_grid [1][1]==3'd5));

    norway_0_next_blue: assume property (@(posedge clk) 
       nation[0] == norway |-> color[1] == blue);

    norway_4_next_blue: assume property (@(posedge clk) 
       nation[4] == norway |-> color[3] == blue);
    
    generate 
       for(i = 1; i < 4; i = i + 1) begin
         norway_next_blue: assume property (@(posedge clk) 
            (nation[i] == norway) |-> ((color[i+1] == blue) || (color [i-1] == blue)));
       end
    endgenerate


//cover to get a trace

    norway_first_cover: cover property (@(posedge clk) 
       (nation[0] == norway));

// cover for uniqueness
          
//         zebra_unique: cover property (@(posedge clk) 
//           ##1 (zebra_grid != $past(zebra_grid)));


`endif //VERIFIC
`endif
endmodule
