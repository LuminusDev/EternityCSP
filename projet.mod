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
int PiecesOrientees[p in PP][o in O] = Pieces[ftoi(floor((p-1)/4))+1][(p+o-2)%4+1];

//Variables
dvar int placement[Lines][Columns] in P; //index de la piece placée sur une case (sans orientation)
dvar int orientation[Lines][Columns] in O; //orientation d'une case
dvar int haut[Lines][Columns] in Colors; //couleur du haut d'une case
dvar int droite[Lines][Columns] in Colors; //couleur de la droite d'une case
dvar int bas[Lines][Columns] in Colors; //couleur du bas d'une case
dvar int gauche[Lines][Columns] in Colors; //couleur de la gauche d'une case

execute{
	var f = cp.factory;
 	var phase1 = f.searchPhase(orientation);
 	var phase2 = f.searchPhase(placement);
 	cp.setSearchPhases(phase1, phase2);
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
    	   (placement[l][c] == ftoi(floor((p-1)/4))+1 && orientation[l][c] == (p-1)%4+1) =>
    		( PiecesOrientees[p][1] == haut[l][c] &&
    		PiecesOrientees[p][2] == droite[l][c] &&
    		PiecesOrientees[p][3] == bas[l][c] &&
    		PiecesOrientees[p][4] == gauche[l][c]  );  
      }  	   
    }
  } 
}