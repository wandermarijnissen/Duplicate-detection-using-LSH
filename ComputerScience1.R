install.packages("dplyr")
install.packages("rjson")
install.packages("tidyverse")
install.packages("lsa")
install.packages("sjmisc")
library("sjmisc")
library("rjson")
library("dplyr")
library("tidyverse")
library("lsa")
rm(list=ls())

setwd("~/Desktop/Computer Science for Business Analytics/Paper")
data <- fromJSON(file = "TVs-all-merged.json")

#check number of unique products
productNumber <- 0
for (p in 1:length(data)){
  productNumber <- productNumber +length(data[[p]])
}

#check which are real duplicates
real_duplicates <- matrix(0, productNumber, productNumber)
j <- 1
for (p in 1:length(data)){
  i <- length(data[[p]])
  if (i == 1) {
    j <- j +1
  } else if (i == 2) {
    real_duplicates[j,j+1] <- 1
    j <- j +2
  } else if (i == 3) {
    real_duplicates[j,j+1] <- 1
    real_duplicates[j,j+2] <- 1
    real_duplicates[j+1,j+2] <- 1
    j <- j +3
  } else if (i == 4) {
    real_duplicates[j,j+1] <- 1
    real_duplicates[j,j+2] <- 1
    real_duplicates[j,j+3] <- 1
    real_duplicates[j+1,j+2] <- 1
    real_duplicates[j+1,j+3] <- 1
    real_duplicates[j+2,j+3] <- 1
    j <- j +4
  }
}

#extract and modify all titles from the data
titles <- 0
for (p in 1:length(data)) {
  i <- length(data[[p]])
  for (k in 1:i) {
    title <- data[[p]][[k]][["title"]]
    if (str_contains(data[[p]][[k]][["featuresMap"]][["Brand"]], "")) {
      title <- paste(title, data[[p]][[k]][["featuresMap"]][["Brand"]])
    }
    titles <- append(titles,title)
  }
}
titles <- titles[-1]
titles <- c(titles)
titles <- tolower(titles)
titles <- gsub('hertz| hertz|-hertz| hz|-hz','hz',titles)
titles <- gsub('-inch| inch| -inch|inches| inches|-inches|\"|\\"','inch',titles)
titles <- gsub('diag|diag.', 'diagonal',titles)
titles <- gsub('\\(|\\)|\\,|\\-|','',titles) #try with & without to see difference in performance

#determine all different brands and brands per product
s <- 0
brands <- c()
for (p in 1:length(data)) {
  i <- length(data[[p]])
  for (k in 1:i) {
    if (str_contains(data[[p]][[k]][["featuresMap"]][["Brand"]], "")) {
      brands <- append(brands, data[[p]][[k]][["featuresMap"]][["Brand"]])
    } 
  }
}
brands <- tolower(brands)
brands <- unique(brands)
product_brands <- c()
for (p in 1:length(data)) {
  i <- length(data[[p]])
  for (k in 1:i) {
    brad <- c(NA)
    for (l in 1:length(brands)) {
      if (str_contains(tolower(data[[p]][[k]][["title"]]), brands[l])) {
        brad <- brands[l]
      }
    }
    if (is.na(brad)) {
      if (str_contains(data[[p]][[k]][["featuresMap"]][["Brand"]], "")) {
        brad <- data[[p]][[k]][["featuresMap"]][["Brand"]]
      }
    }
    product_brands <- append(product_brands,brad)
  }
}
product_brands <- tolower(product_brands)
for (i in 1:1624) {
  if (is.na(product_brands[i])){
    product_brands[i] <- 0
  }
}

fraction_of_comparisons <- rep(0,7)
average_metrics <- matrix(0,6,7)
band_numbers <- c(1,10,25,50,100,250,500)
for(band_number in band_numbers){  
  #define function used in bootstrap that returns all 6 metrics
  detect <- function(subset, alpha) {
    titles_subset <- 0
    subset_brands <- 0
    for (i in subset) {
      titles_subset <- append(titles_subset,titles[i])
      subset_brands<- append(subset_brands,product_brands[i])
    }
    subset_brands <- subset_brands [-1]
    titles_subset <- titles_subset[-1]
    word <- c()
    x1 <- c(1:25)
    # Find all model words and add tv brands to the model words
    for (i in x1) {
      word <- c(word, word(titles_subset, i))
    }
    word <- unique(word)
    word <- na.omit (word)
    model_word <- c()
    model_word <- str_extract(word, "[a-zA-Z0-9]*(([0-9]+[^0-9, ]+)|([^0-9, ]+[0-9]+))[a-zA-Z0-9]*")
    model_word <- na.omit(model_word)
    model_word <- c(model_word)
    model_word <- unique(model_word)
    model_word <- append(model_word, brands)
    
    #Create a binary matrix which has a 1 if a model word is present in the specific title   
    binary_matrix <- matrix(0,length(subset),length(model_word))
    for (p in 1:length(subset)) {
      titels <- titles_subset[p]
      end <- FALSE
      i <- 1
      while (end == FALSE) {
        mw <- word(titels, i)
        if(is.na(mw)) {
          end = TRUE
        } else for (j in 1:length(model_word)) {
          if(mw == model_word[j]) {
            binary_matrix[p,j] <- 1 
          }
        }
        i = i+1
      }
    }
    binary_matrix <- t(binary_matrix)
    
    #create signature matrix through minhashing
    permutation_matrix <- t(matrix(0, nrow(binary_matrix),600))
    for (i in 1:600) {
      set.seed(i)
      permutation_matrix[i,] <- matrix(sample(seq(1:nrow(binary_matrix))))
    }
    permutation_matrix <- t(permutation_matrix)
    signature <- matrix(1400, nrow = ncol(permutation_matrix), ncol = ncol(binary_matrix))
    for (r in 1:nrow(binary_matrix)) {
      for (c in 1:ncol(binary_matrix)) {
        if (binary_matrix[r,c] == 1) {
          for (i in 1:ncol(permutation_matrix))
            if (permutation_matrix[r,i] < signature[i,c]) {
              signature[i,c] <- permutation_matrix[r,i]
            }
        }
      }
    }
    
    #LSH
    bands <- band_number
    rows <- 500/bands
    candidates <- matrix(0, nrow = ncol(signature), ncol = ncol(signature))
    end <- FALSE
    i <- 1 
    j <- rows #number of rows per band
    while ( end == FALSE) {
      band.matrix <- matrix(signature[i:j,], nrow = rows, ncol = ncol(signature))
      for (t in 1:ncol(signature)){
        for (s in t:ncol(signature)) {
          if (all(band.matrix[,t] == band.matrix[,s])) {
            candidates[t,s] <- 1
          } 
        } 
        candidates[t,t] <- 0
      }
      i <- i + rows
      j <- j + rows
      if (i > bands*rows) {    
        end <- TRUE
      }
    }
    
    #remove candidates that do not have the same brands
    candidates_subset <- candidates
    cos <- matrix(0, nrow = ncol(signature), ncol = ncol(signature))
    for (t in 1:ncol(candidates)) {
      for (s in t:ncol(candidates)) {
        if (candidates_subset[t,s] == 1 & subset_brands[t] != subset_brands[s]) {
          candidates_subset[t,s] <- 0
        }
        #determine whether candidates are similar enough to be marked as duplicates
        if (candidates_subset[t,s] == 1) {
          cos[t,s] <- cosine(signature[,t],signature[,s])
          if(cos[t,s] < alpha) {
            candidates_subset[t,s] <- 0
          }
        }
      }
    }
    
    #check how many of the subset are actually duplicates
    duplicates <- matrix(0,nrow= length(subset), ncol=length(subset))
    for (j in 1:length(subset)) {
      for (i in 1:length(subset)) {
        duplicates[j,i] <- real_duplicates[subset[j],subset[i]]
      }
    }
    
    
    #calculate and return results
    check <- duplicates + candidates
    check1 <- duplicates + candidates_subset
    duplicates_found <- sum(check == 2)
    duplicates_found1 <- sum(check1 == 2) 
    pair_completeness <- duplicates_found/sum(duplicates)
    pair_quality <- duplicates_found/sum(candidates)
    f1_star <- 2/ ((1/pair_completeness) + (1/pair_quality))
    precision <- duplicates_found1/sum(candidates_subset)
    recall <- duplicates_found1/sum(duplicates)
    f1 <- 2/ ((1/precision) + (1/recall))
    answer <- c(pair_completeness, pair_quality, f1_star, precision, recall, f1)
    return(answer)
  }
  
  
  #write loop for 5 bootstraps
  bootstraps <- 5
  f1 <- 0
  overviewtrain <- c()
  overviewtest <- c()
  param_best <- c()
  for(b in 1:bootstraps){
    train <- c()
    test <- c()
    set.seed(b)
    draws <- sample(1:length(titles),replace=TRUE)
    for(i in 1:length(titles)){
      if(i %in% draws){
        train <- append(train,i)
      } else {
        test <- append(test,i)
      }
    }
    #grid-search to find optimal threshold
    alpha_best <- 0
    grid <- c(0.9,0.8,0.95)
    F1best <- 0
    for (i in grid) {
      overviewtrain <- append(overviewtrain,detect(train,i))
      if (overviewtrain[6] > F1best) {
        F1best <- overviewtrain[6]
        alpha_best <- i
        
      }
      overviewtrain <- 0 
    }
    param_best <- append(param_best,alpha_best)
    overviewtest <- append(overviewtest,detect(test,alpha_best))
    overviewtest
  }

  if(band_number==1){
    c <- 1
  } else if(band_number==10){
    c <- 2
  } else if(band_number==25){
    c <- 2
  } else if(band_number==50){
    c <- 2
  } else if(band_number==100){
    c <- 2
  } else if(band_number==250){
    c <- 2
  } else if(band_number==500){
    c <- 2
  } 
  
  final_metrics <- matrix(overviewtest,6,bootstraps)
  for(r in 1:6){
    average <- 0 
    for(i in 1:bootstraps){
      average <- average + final_metrics[r,i]/bootstraps
    }
    average_metrics[r,c] <- average
  }
  fraction_of_comparisons[c] <- sum(candidates)/((length(subset))^2-(length(subset))/2)
}

#create figures
table_complete <- cbind(average_metrics[1,],fraction_of_comparisons)
table_quality <- cbind(average_metrics[2,],fraction_of_comparisons)
table_f1star <- cbind(average_metrics[3,],fraction_of_comparisons)
table_f1 <- cbind(average_metrics[6,],fraction_of_comparisons)

par(mfrow=c(2,2))
plot(table_complete[,2], table_complete[,1], ylab = "Pair completness", xlab = "Fraction of comparisons", type = "o" ,xlim=c(0,1), ylim=c(0,1))
plot(table_quality[,2], table_quality[,1], ylab = "Pair quality", xlab = "Fraction of comparisons", type = "o" ,xlim=c(0,0.2), ylim=c(0,0.2))
plot(table_f1star[,2], table_f1star[,1], ylab = "F_1*", xlab = "Fraction of comparisons", type = "o" ,xlim=c(0,1), ylim=c(0,0.4))
plot(table_f1[,2], table_f1[,1], ylab = "F_1", xlab = "Fraction of comparisons", type = "o" ,xlim=c(0,1), ylim=c(0,0.4))