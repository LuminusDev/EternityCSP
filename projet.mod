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

int Pieces[P][O] = ...;
//{int} PiecesSet[P] = [];
// toutes les pieces avec les 4 orientations possibles
int PiecesOrientees[p in PP][o in O] = Pieces[ftoi(floor((p-1)/4))+1][(p+o-2)%4+1];

// ensemble des pieces contenant un 1 (pour aller sur un bord)
{int} PiecesBords = {};

// ensemble des pieces contenant deux 1 d'affilés (pour aller sur un coin) 
{int} PiecesCoins = {};
  
execute{
	for(var p in P){
		if( Pieces[p][1] == 1 
								|| Pieces[p][2] == 1
								|| Pieces[p][3] == 1
								|| Pieces[p][4] == 1 ){
			PiecesBords.add(p);
		}
		if ( (Pieces[p][1] == 1 && Pieces[p][2] == 1)
								|| (Pieces[p][2] == 1 && Pieces[p][3] == 1)
								|| (Pieces[p][3] == 1 && Pieces[p][4] == 1)
								|| (Pieces[p][4] == 1 && Pieces[p][1] == 1)){
        	PiecesCoins.add(p);
        }
        // creation des ensembles de couleur
//        PiecesSet[p].add(Pieces[p][1]);
//        PiecesSet[p].add(Pieces[p][2]);
//        PiecesSet[p].add(Pieces[p][3]);
//        PiecesSet[p].add(Pieces[p][4]);				  
 	}	   
}  

//Variables
dvar int placement[Lines][Columns] in P; //index de la piece placée sur une case (sans orientation)
dvar int orientation[Lines][Columns] in O; //orientation d'une case
dvar int haut[Lines][Columns] in Colors; //couleur du haut d'une case
dvar int droite[Lines][Columns] in Colors; //couleur de la droite d'une case
dvar int bas[Lines][Columns] in Colors; //couleur du bas d'une case
dvar int gauche[Lines][Columns] in Colors; //couleur de la gauche d'une case
//dvar int placeOriente[Lines][Columns] in PP;

execute{
	var f = cp.factory;
 	var phase1 = f.searchPhase(orientation,
 			f.selectSmallest(f.domainMin()),
 			f.selectLargest(f.valueIndex(Pieces)));
 	var phase2 = f.searchPhase(placement,
 			f.selectLargest(f.domainMin()),
 			f.selectLargest(f.valueIndex(Pieces)));
 	cp.setSearchPhases(phase1, phase2);
}

subject to {
  // toutes les pièces ont un emplacement différent
  allDifferent(placement);

  // tous les bords n'ont pas de couleurs  
  forall(c in Columns){
	haut[1][c] == 1;
	bas[NbLines][c] == 1;
 	// fixation des pieces sur les bords
 	or(p in PiecesBords)placement[1][c] == p;
	or(p in PiecesBords)placement[NbLines][c] == p;  
  }
  
  forall(l in Lines){
	gauche[l][1] == 1;
	droite[l][NbColumns] == 1;
	// fixation des pieces sur les bords
	or(p in PiecesBords)placement[l][1] == p;
	or(p in PiecesBords)placement[l][NbColumns] == p;  
  }
  
  // fixation des pieces dans les coins
  or(p in PiecesCoins)placement[1][1] == p;
  or(p in PiecesCoins)placement[1][NbColumns] == p;
  or(p in PiecesCoins)placement[NbLines][1] == p;
  or(p in PiecesCoins)placement[NbLines][NbColumns] == p;
  
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
  
  forall(l in Lines){
    forall(c in Columns){
      
//      placeOriente[l][c] == 4*(placement[l][c]-1) + orientation[l][c]-1;
      
//      forall(p in P){
//        (placement[l][c] == p) => (placeOriente[l][c] >= 4*(p-1) && placeOriente[l][c] <= 4*(p-1)+3);
//      }
//      
//      forall(o in O){
//        (orientation[l][c] == o) => (placeOriente[l][c]%4 == o-1);
//      }        
      
      forall(p in PP){
        // Liaison couleurs / Pieces : 1 pièce correspond à une case et une orientation
    	   (placement[l][c] == ftoi(floor((p-1)/4))+1 && orientation[l][c] == (p-1)%4+1) =>
    		( PiecesOrientees[p][1] == haut[l][c] &&
    		PiecesOrientees[p][2] == droite[l][c] &&
    		PiecesOrientees[p][3] == bas[l][c] &&
    		PiecesOrientees[p][4] == gauche[l][c]  );
    		
    	// Une piece placée limite les couleurs de la case à celles de la pièce
    	// Augmente la durée d'exécution (1 400 000 de contraintes ajoutées)
    	// 40sec au lieu de 2sec
//    	(placement[l][c] == ftoi(floor((p-1)/4))+1) =>
//    	 (or(pi in PiecesSet[ftoi(floor((p-1)/4))+1])pi == haut[l][c] &&
//    	  or(pi in PiecesSet[ftoi(floor((p-1)/4))+1])pi == bas[l][c] &&
//    	  or(pi in PiecesSet[ftoi(floor((p-1)/4))+1])pi == gauche[l][c] &&
//    	  or(pi in PiecesSet[ftoi(floor((p-1)/4))+1])pi == droite[l][c]
//    	);
      }  	   
    }
  } 
}