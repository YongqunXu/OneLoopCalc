{
box[0,0,2,0] -> 
 + box[0,0,1,0]*((d-2)/(2*eta-180))
,
box[1,0,2,0] -> 
 + box[1,0,1,0]*((d-3)/(eta+10))
 + box[0,0,1,0]*((-d+2)/(2*eta^2-160*eta-1800))
,
box[0,1,2,1] -> 
 + box[0,1,1,1]*(((d-4)*eta-140*d+560)/(eta^2-280*eta+17100))
 + box[0,1,0,1]*((d-3)/(eta^2-280*eta+17100))
 + box[0,0,1,0]*((-d+2)/(2*eta^3-740*eta^2+84600*eta-3078000))
,
box[1,1,2,1] -> 
 + box[1,1,1,1]*((d-5)/(eta+10))
 + box[0,1,1,1]*((50*d-200)/(eta^3-270*eta^2+14300*eta+171000))
 + box[0,1,0,1]*(((d-3)*eta-140*d+420)/(50*eta^3-13500*eta^2+715000*eta+8550000))
 + box[0,0,1,0]*((-d+2)/(2*eta^4-720*eta^3+77200*eta^2-2232000*eta-30780000))
}
