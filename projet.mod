/* ------------------------------------------------------------

Problem Description
-------------------

Vous disposez d’un plateau de taille n*m et n*m pièces
ayant quatre bords de couleur différente. Le but est de placer les
différentes pièces de façon à ce que deux pièces qui se touchent 
aient la même couleur (la bordure n’a pas de couleur
et est représentée par le symbole « − »).

L'objectif est d'obtenir un placement réalisable.

------------------------------------------------------------ */
 
using CP;

int NbColors = ...;
range Colors = 1..NbColors;
int NbLines = ...;
range Lines = 1..NbLines;
int NbColumns = ...;
range Columns = 1..NbColumns;
int NbPieces = NbLines*NbColumns;
int NbOrientations = ...;
range O = 1..NbOrientations;
range P = 1..NbPieces;
range PP = 1..NbPieces*NbOrientations;

tuple Piece {
  int color[1..4];
};

Piece Pieces[1..NbPieces] = ...;
 /*Piece PiecesOrientees[p in PP] = <[ Pieces[floor((p-1)/4)+1].color[(p-1)%4+1],
									Pieces[floor((p-1)/4)+1].color[p%4+1],
									Pieces[floor((p-1)/4)+1].color[(p+1)%4+1],
									Pieces[floor((p-1)/4)+1].color[(p+2)%4+1] ]>;
*/
Piece PiecesOrientees[p in PP] = <[ q : Pieces[floor((p-1)/4) + 1 ].color[(p-1+q-1)%4 +1] | q in O]>;

execute{
 	for(var p in P){
 		PiecesOrientees[4*(p-1)+1] = 
 		PiecesOrientees[4*(p-1)+2] = 
 		PiecesOrientees[4*(p-1)+3] = 
 		PiecesOrientees[4*(p-1)+4] =   
  	} 	   
}  
//{Piece} PiecesEns = {Pieces[i] | i in 1..NbPieces};

//Variables
dvar int placement[Lines][Columns] in P;
dvar int orientation[Lines][Columns] in O;
dvar int haut[Lines][Columns] in Colors;
dvar int droite[Lines][Columns] in Colors;
dvar int bas[Lines][Columns] in Colors;
dvar int gauche[Lines][Columns] in Colors;

dexpr int pieceOrientee[l in Lines][c in Columns] = 4*placement[l][c] + orientation[l][c] -1 ;
//dexpr int colorPiece[p in 1..NbPieces][i in 1..4] = Pieces[p].color[((i-1+ori entation[p]-1)%4)+1];

execute {
  cp.param.FailLimit = 10000;
}

subject to {
  // toutes les pièces ont un emplacement différent
  allDifferent(placement);

  // tous les bords n'ont pas de couleurs  
  forall(c in Columns){
	haut[1][c] == 1;
	bas[NbLines][c] == 1;  	  
  }
  
  forall(l in Lines){
	gauche[l][1] == 1;
	droite[l][NbColumns] == 1;  	  
  }
  
  // Contraintes match couleurs
  forall(l in 2..NbLines){
  	forall( c in Columns){
  		haut[l][c] == bas[l-1][c];
    }  	    
  }

  forall(c in 2..NbColumns){
    forall(l in Lines){
      gauche[l][c] == droite[l][c-1];
   	}
  }  
  
  // Liaison couleurs / Pieces : 1 pièce correspond à une case et une orientation
  forall(l in Lines){
    forall(c in Columns){
    	 forall(p in PP){
    	   (placement[l][c] == (p-1)/4+1 && orientation[l][c] == (p-1)%4+1) =>
    		(pieceOrientee[p].color[1] == haut[l][c] &&
    		pieceOrientee[p].color[2] == droite[l][c] &&
    		pieceOrientee[p].color[3] == bas[l][c] &&
    		pieceOrientee[p].color[4] == gauche[l][c]  );  
      }    	   
    }
  }   
}